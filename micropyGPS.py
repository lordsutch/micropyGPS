"""
# MicropyGPS - a GPS NMEA sentence parser for Micropython/Python 3.X
# Copyright (c) 2017 Michael Calvin McCoy (calvin.mccoy@protonmail.com)
# The MIT License (MIT) - see LICENSE file
"""

# TODO:
# Time Since First Fix
# Distance/Time to Target
# More Helper Functions
# Dynamically limit sentences types to parse

from math import floor, modf
try:
    from math import inf
except ImportError:
    inf = float('Inf')

# Import utime or time for fix time handling
try:
    # Assume running on MicroPython
    import utime
except ImportError:
    # Otherwise default to time module for non-embedded implementations
    # Should still support millisecond resolution.
    import time


class MicropyGPS(object):
    """GPS NMEA Sentence Parser. Creates object that stores all relevant GPS data and statistics.
    Parses sentences one character at a time using update(). """

    # Max Number of Characters a valid sentence can be (based on GGA sentence)
    SENTENCE_LIMIT = 90
    __HEMISPHERES = ('N', 'S', 'E', 'W')
    __NO_FIX = 1
    __FIX_2D = 2
    __FIX_3D = 3
    __DIRECTIONS = ('N', 'NNE', 'NE', 'ENE', 'E', 'ESE', 'SE', 'SSE', 'S', 'SSW', 'SW', 'WSW', 'W',
                    'WNW', 'NW', 'NNW')
    __MONTHS = ('January', 'February', 'March', 'April', 'May',
                'June', 'July', 'August', 'September', 'October',
                'November', 'December')

    def __init__(self, local_offset=0, location_formatting='ddm', century=20):
        """
        Setup GPS Object Status Flags, Internal Data Registers, etc
            local_offset (int): Timezone Difference to UTC in hours
            location_formatting (str): Style For Presenting Longitude/Latitude:
                                       Decimal Degree Minute (ddm) - 40° 26.767′ N
                                       Degrees Minutes Seconds (dms) - 40° 26′ 46″ N
                                       Decimal Degrees (dd) - 40.446° N
            century (int): Default century for messages with two-digit years
        """

        #####################
        # Object Status Flags
        self.sentence_active = False
        self.active_segment = 0
        self.process_crc = False
        self.gps_segments = []
        self.crc_xor = 0
        self.char_count = 0
        self.fix_time = 0

        #####################
        # Sentence Statistics
        self.crc_fails = 0
        self.clean_sentences = 0
        self.parsed_sentences = 0

        #####################
        # Logging Related
        self.log_handle = None
        self.log_en = False

        #####################
        # Data From Sentences
        # Time
        self.timestamp = (0, 0, 0.0)
        self.date = (0, 0, 0)
        self.local_offset = local_offset * 3600
        self.century = century

        # Position/Motion
        self._latitude = (0, 0.0, 'N')
        self._longitude = (0, 0.0, 'W')
        self.coord_format = location_formatting
        self.speed = (0.0, 0.0, 0.0)
        self.course = 0.0
        self.altitude = 0.0
        self.geoid_height = 0.0

        # GPS Info
        self.satellites_in_view = 0
        self.satellites_in_use = 0
        self.satellites_used = dict()
        self.last_sv_sentence = 0
        self.total_sv_sentences = 0
        self.satellite_data = dict()
        self.hdop = inf
        self.pdop = inf
        self.vdop = inf
        self.valid = False
        self.fix_stat = 0
        self.fix_type = 1
        self.dgps_age = None
        self.dgps_station = None

    ########################################
    # Coordinates Translation Functions
    ########################################
    @property
    def latitude(self):
        """Format Latitude Data Correctly"""
        if self.coord_format == 'dd':
            decimal_degrees = self._latitude[0] + (self._latitude[1] / 60)
            return (decimal_degrees, self._latitude[2])
        elif self.coord_format == 'dms':
            minute_parts = modf(self._latitude[1])
            seconds = round(minute_parts[0] * 60)
            return (self._latitude[0], int(minute_parts[1]), seconds, self._latitude[2])
        else:
            return self._latitude

    @property
    def longitude(self):
        """Format Longitude Data Correctly"""
        if self.coord_format == 'dd':
            decimal_degrees = self._longitude[0] + (self._longitude[1] / 60)
            return (decimal_degrees, self._longitude[2])
        elif self.coord_format == 'dms':
            minute_parts = modf(self._longitude[1])
            seconds = round(minute_parts[0] * 60)
            return (self._longitude[0], int(minute_parts[1]), seconds, self._longitude[2])
        else:
            return self._longitude

    ########################################
    # Logging Related Functions
    ########################################
    def start_logging(self, target_file, mode="append"):
        """
        Create GPS data log object
        """
        # Set Write Mode Overwrite or Append
        mode_code = 'w' if mode == 'new' else 'a'

        try:
            self.log_handle = open(target_file, mode_code)
        except AttributeError:
            print("Invalid FileName")
            return False

        self.log_en = True
        return True

    def stop_logging(self):
        """
        Closes the log file handler and disables further logging
        """
        try:
            self.log_handle.close()
        except AttributeError:
            print("Invalid Handle")
            return False

        self.log_en = False
        return True

    def write_log(self, log_string):
        """Attempts to write the last valid NMEA sentence character to the active file handler
        """
        try:
            self.log_handle.write(log_string)
        except TypeError:
            return False
        return True

    def parse_time(self, utc_string):
        '''Convert time in NMEA sentences to h:m:s, accounting for offset.

        :param utc_string string containing time in NMEA format
        :return: boolean reflecting success/failure'''
        if utc_string:  # Possible timestamp found
            try:
                hours = int(utc_string[0:2])
                minutes = int(utc_string[2:4])
                seconds = float(utc_string[4:])
            except ValueError:
                return False

            if self.local_offset:
                total_secs = (hours*3600 + minutes * 60 + seconds +
                              self.local_offset) % 86400
                hours = (total_secs // 3600)
                minutes = (total_secs % 3600) // 60
                seconds = total_secs % 60
            self.timestamp = (hours, minutes, seconds)
        else:  # No Time stamp yet
            self.timestamp = (0, 0, 0.0)
        return True

    ########################################
    # Sentence Parsers
    ########################################
    def gprmc(self):
        """Parse Recommended Minimum Specific GPS/Transit data (RMC)Sentence.
        Updates UTC timestamp, latitude, longitude, Course, Speed, Date, and fix status
        """
        if not self.parse_time(self.gps_segments[1]):
            return False

        # Date stamp
        try:
            date_string = self.gps_segments[9]

            # If GPS isn't sending ZDA messages, century is set in constructor
            if date_string:  # Possible date stamp found
                day = int(date_string[0:2])
                month = int(date_string[2:4])
                year = int(date_string[4:6]) + 100*self.century
                self.date = (day, month, year)
            else:  # No Date stamp yet
                self.date = (0, 0, 0)

        except ValueError:  # Bad Date stamp value present
            return False

        # Check Receiver Data Valid Flag
        if self.gps_segments[2] == 'A':  # Data from Receiver is Valid/Has Fix

            # Longitude / Latitude
            try:
                # Latitude
                l_string = self.gps_segments[3]
                lat_degs = int(l_string[0:2])
                lat_mins = float(l_string[2:])
                lat_hemi = self.gps_segments[4]

                # Longitude
                l_string = self.gps_segments[5]
                lon_degs = int(l_string[0:3])
                lon_mins = float(l_string[3:])
                lon_hemi = self.gps_segments[6]
            except ValueError:
                return False

            if lat_hemi not in self.__HEMISPHERES:
                return False

            if lon_hemi not in self.__HEMISPHERES:
                return False

            # Speed
            try:
                spd_knt = float(self.gps_segments[7])
            except ValueError:
                return False

            # Course
            try:
                if self.gps_segments[8]:
                    course = float(self.gps_segments[8])
                else:
                    course = 0.0
            except ValueError:
                return False

            # TODO - Add Magnetic Variation

            # Update Object Data
            self._latitude = (lat_degs, lat_mins, lat_hemi)
            self._longitude = (lon_degs, lon_mins, lon_hemi)
            # Include mph and hm/h
            self.speed = (spd_knt, spd_knt * 1.151, spd_knt * 1.852)
            self.course = course
            self.valid = True

            # Update Last Fix Time
            self.new_fix_time()

        else:  # Clear Position Data if Sentence is 'Invalid'
            self._latitude = (0, 0.0, 'N')
            self._longitude = (0, 0.0, 'W')
            self.speed = (0.0, 0.0, 0.0)
            self.course = 0.0
            self.valid = False

        return True

    def gpgll(self):
        """Parse Geographic Latitude and Longitude (GLL)Sentence. Updates UTC timestamp, latitude,
        longitude, and fix status"""

        # UTC Timestamp
        if not self.parse_time(self.gps_segments[5]):
            return False

        # Check Receiver Data Valid Flag
        if self.gps_segments[6] == 'A':  # Data from Receiver is Valid/Has Fix

            # Longitude / Latitude
            try:
                # Latitude
                l_string = self.gps_segments[1]
                lat_degs = int(l_string[0:2])
                lat_mins = float(l_string[2:])
                lat_hemi = self.gps_segments[2]

                # Longitude
                l_string = self.gps_segments[3]
                lon_degs = int(l_string[0:3])
                lon_mins = float(l_string[3:])
                lon_hemi = self.gps_segments[4]
            except ValueError:
                return False

            if lat_hemi not in self.__HEMISPHERES:
                return False

            if lon_hemi not in self.__HEMISPHERES:
                return False

            # Update Object Data
            self._latitude = (lat_degs, lat_mins, lat_hemi)
            self._longitude = (lon_degs, lon_mins, lon_hemi)
            self.valid = True

            # Update Last Fix Time
            self.new_fix_time()

        else:  # Clear Position Data if Sentence is 'Invalid'
            self._latitude = (0, 0.0, 'N')
            self._longitude = (0, 0.0, 'W')
            self.valid = False

        return True

    def gpvtg(self):
        """Parse Track Made Good and Ground Speed (VTG) Sentence. Updates speed and course"""
        try:
            course = float(self.gps_segments[1]) if self.gps_segments[1] else 0.0
            spd_knt = float(self.gps_segments[5]) if self.gps_segments[5] else 0.0
        except ValueError:
            return False

        # Include mph and km/h
        self.speed = (spd_knt, spd_knt * 1.151, spd_knt * 1.852)
        self.course = course
        return True

    def gpgga(self):
        """Parse Global Positioning System Fix Data (GGA) Sentence. Updates UTC timestamp, latitude, longitude,
        fix status, satellites in use, Horizontal Dilution of Precision (HDOP), altitude, geoid height and fix status"""

        # UTC Timestamp
        if not self.parse_time(self.gps_segments[1]):
            return False

        try:
            # Number of Satellites in Use
            satellites_in_use = int(self.gps_segments[7])

            # Get Fix Status
            fix_stat = int(self.gps_segments[6])

        except (ValueError, IndexError):
            return False

        try:
            # Horizontal Dilution of Precision
            hdop = float(self.gps_segments[8])
        except (ValueError, IndexError):
            hdop = inf

        # Process Location and Speed Data if Fix is GOOD
        if fix_stat:

            # Longitude / Latitude
            try:
                # Latitude
                l_string = self.gps_segments[2]
                lat_degs = int(l_string[0:2])
                lat_mins = float(l_string[2:])
                lat_hemi = self.gps_segments[3]

                # Longitude
                l_string = self.gps_segments[4]
                lon_degs = int(l_string[0:3])
                lon_mins = float(l_string[3:])
                lon_hemi = self.gps_segments[5]
            except ValueError:
                return False

            if lat_hemi not in self.__HEMISPHERES:
                return False

            if lon_hemi not in self.__HEMISPHERES:
                return False

            # Altitude / Height Above Geoid
            try:
                altitude = float(self.gps_segments[9])
                geoid_height = float(self.gps_segments[11])
            except ValueError:
                altitude = 0
                geoid_height = 0

            # Update Object Data
            self._latitude = (lat_degs, lat_mins, lat_hemi)
            self._longitude = (lon_degs, lon_mins, lon_hemi)
            self.altitude = altitude
            self.geoid_height = geoid_height

        # Update Object Data
        if self.satellites_in_use <= 12 or satellites_in_use > 12:
            # If true value > 12, don't override whatever xxGNS is providing
            # since some units obey NMEA limit of 12 in xxRMC sentence
            self.satellites_in_use = satellites_in_use

        self.hdop = hdop
        self.fix_stat = fix_stat

        # If Fix is GOOD, update fix timestamp
        if fix_stat:
            self.new_fix_time()

        return True

    def gpgsa(self):
        """Parse GNSS DOP and Active Satellites (GSA) sentence. Updates GPS fix type, list of satellites used in
        fix calculation, Position Dilution of Precision (PDOP), Horizontal Dilution of Precision (HDOP), Vertical
        Dilution of Precision, and fix status"""

        # Fix Type (None,2D or 3D)
        try:
            fix_type = int(self.gps_segments[2])
        except ValueError:
            return False

        # Read All (up to 12) Available PRN Satellite Numbers
        sats_used = set()
        for sats in range(12):
            sat_number_str = self.gps_segments[3 + sats]
            if sat_number_str:
                try:
                    sat_number = int(sat_number_str)
                    sats_used.add(sat_number)
                except ValueError:
                    return False
            else:
                break

        # PDOP,HDOP,VDOP
        try:
            pdop = float(self.gps_segments[15])
            hdop = float(self.gps_segments[16])
            vdop = float(self.gps_segments[17])
        except ValueError:
            return False

        # Update Object Data
        self.fix_type = fix_type

        # If Fix is GOOD, update fix timestamp
        if fix_type > self.__NO_FIX:
            self.new_fix_time()

        talker = self.talker
        if len(self.gps_segments) >= 20:
            try:
                systemID = int(self.gps_segments[18], 16)
            except ValueError:
                systemID = 1
            talker = self.nmea_system_ids[systemID]
            self.satellites_used[talker] = sats_used
        else:
            if talker not in self.satellites_used:
                self.satellites_used[talker] = set()
            for t, satinfo in self.satellite_data.items():
                for signum, sats_in_view in satinfo.items():
                    sats_in_view = set(sats_in_view.keys())
                    # Find satellite list including sats in this sentence
                    if sats_in_view & sats_used:
                        self.satellites_used[talker] -= sats_in_view
            self.satellites_used[talker] |= sats_used

        self.hdop = hdop
        self.vdop = vdop
        self.pdop = pdop

        return True

    def gpgsv(self):
        """Parse Satellites in View (GSV) sentence. Updates number of SV Sentences,the number of the last SV sentence
        parsed, and data on each satellite present in the sentence"""
        try:
            num_sv_sentences = int(self.gps_segments[1])
            current_sv_sentence = int(self.gps_segments[2])
            sats_in_view = int(self.gps_segments[3])
        except ValueError:
            return False

        # Create a blank dict to store all the satellite data from this sentence in:
        # satellite PRN is key, tuple containing telemetry is value
        satellite_dict = dict()
        sat_segment_limit = 4*(len(self.gps_segments) // 4)
        # Try to recover data for up to 4 satellites in sentence
        for sats in range(4, sat_segment_limit, 4):

            # If a PRN is present, grab satellite data
            if self.gps_segments[sats]:
                try:
                    sat_id = int(self.gps_segments[sats])
                except (ValueError,IndexError):
                    return False

                try:  # elevation can be null (no value) when not tracking
                    elevation = int(self.gps_segments[sats+1])
                except (ValueError,IndexError):
                    elevation = None

                try:  # azimuth can be null (no value) when not tracking
                    azimuth = int(self.gps_segments[sats+2])
                except (ValueError,IndexError):
                    azimuth = None

                try:  # SNR can be null (no value) when not tracking
                    snr = int(self.gps_segments[sats+3])
                except (ValueError,IndexError):
                    snr = None
            # If no PRN is found, then the sentence has no more satellites to read
            else:
                break

            # Add Satellite Data to Sentence Dict
            satellite_dict[sat_id] = (elevation, azimuth, snr)

        # Update Object Data
        self.total_sv_sentences = num_sv_sentences
        self.last_sv_sentence = current_sv_sentence

        signum = 1
        if (len(self.gps_segments) % 4) != 1:
            try:
                pos = (len(self.gps_segments) // 4)*4
                signum = int(self.gps_segments[pos], 16)
            except ValueError:
                pass

        # For a new set of sentences, we either clear out the existing sat data or
        # update it as additional SV sentences are parsed
        if self.talker not in self.satellite_data:
            self.satellite_data[self.talker] = dict()

        if current_sv_sentence == 1:
            self.satellite_data[self.talker] = {signum: satellite_dict}
        elif signum in self.satellite_data[self.talker]:
            self.satellite_data[self.talker][signum].update(satellite_dict)
        else:
            self.satellite_data[self.talker][signum] = satellite_dict

        if current_sv_sentence == num_sv_sentences:
            self.satellites_in_view = 0
            for sigdict in self.satellite_data.values():
                self.satellites_in_view += sum(len(x) for x in sigdict.values())
        return True

    def gpzda(self):
        """Parse GNSS Time and Date (ZDA) sentence. Updates time and date."""
        # UTC Timestamp
        if not self.parse_time(self.gps_segments[1]):
            return False

        # Date stamp
        try:
            day = int(self.gps_segments[2])
            month = int(self.gps_segments[3])
            year = int(self.gps_segments[4])
            self.century = year // 100
            self.date = (day, month, year)
        except ValueError:  # Bad Date stamp value present
            return False

        # Could parse timezone data in positions 5 to 6 if any GPS supports it
        return True

    def gpgns(self):
        """Parse GNSS fix data (GNS) sentence. Updates time, lon/lat,
        satellites used, hdop, altitude, per-GNSS positioning mode,
        geoid separation, and DGPS info."""
        # UTC Timestamp
        if not self.parse_time(self.gps_segments[1]):
            return False

        posMode = self.gps_segments[6]
        if any((x in posMode for x in ('E', 'F', 'R', 'A', 'D'))):
            # Longitude / Latitude
            try:
                # Latitude
                l_string = self.gps_segments[2]
                lat_degs = int(l_string[0:2])
                lat_mins = float(l_string[2:])
                lat_hemi = self.gps_segments[3]

                # Longitude
                l_string = self.gps_segments[4]
                lon_degs = int(l_string[0:3])
                lon_mins = float(l_string[3:])
                lon_hemi = self.gps_segments[5]
            except ValueError:
                return False

            if lat_hemi not in self.__HEMISPHERES:
                return False

            if lon_hemi not in self.__HEMISPHERES:
                return False

            try:
                altitude = float(self.gps_segments[9])
                geoid_height = float(self.gps_segments[10])
            except ValueError:
                altitude = 0
                geoid_height = 0

            # Update Object Data
            self._latitude = (lat_degs, lat_mins, lat_hemi)
            self._longitude = (lon_degs, lon_mins, lon_hemi)
            self.altitude = altitude
            self.geoid_height = geoid_height

            self.new_fix_time()

        try:
            self.satellites_in_use = int(self.gps_segments[7])
        except ValueError:
            pass

        try:
            self.hdop = float(self.gps_segments[8])
        except ValueError:
            self.hdop = 0

        try:
            self.dgps_age = float(self.gps_segments[11])
        except ValueError:
            self.dgps_age = None

        try:
            self.dgps_station = float(self.gps_segments[12])
        except ValueError:
            self.dgps_station = None

        return True

    ##########################################
    # Data Stream Handler Functions
    ##########################################

    def new_sentence(self):
        """Adjust Object Flags in Preparation for a New Sentence"""
        self.gps_segments = ['']
        self.active_segment = 0
        self.crc_xor = 0
        self.sentence_active = True
        self.process_crc = True
        self.char_count = 0

    def update(self, new_char):
        """Process a new input char and updates GPS object if necessary based on special characters ('$', ',', '*')
        Function builds a list of received string that are validate by CRC prior to parsing by the  appropriate
        sentence function. Returns sentence type on successful parse, None otherwise"""

        valid_sentence = False

        # Validate new_char is a printable char
        ascii_char = ord(new_char)

        if 10 <= ascii_char <= 126:
            self.char_count += 1

            # Write Character to log file if enabled
            if self.log_en:
                self.write_log(new_char)

            # Check if a new string is starting ($)
            if new_char == '$':
                self.new_sentence()
                return None

            elif self.sentence_active:

                # Check if sentence is ending (*)
                if new_char == '*':
                    self.process_crc = False
                    self.active_segment += 1
                    self.gps_segments.append('')
                    return None

                # Check if a section is ended (,), Create a new substring to feed
                # characters to
                elif new_char == ',':
                    self.active_segment += 1
                    self.gps_segments.append('')

                # Store All Other printable character and check CRC when ready
                else:
                    self.gps_segments[self.active_segment] += new_char

                    # When CRC input is disabled, sentence is nearly complete
                    if not self.process_crc:

                        if len(self.gps_segments[self.active_segment]) == 2:
                            try:
                                final_crc = int(self.gps_segments[self.active_segment], 16)
                                if self.crc_xor == final_crc:
                                    valid_sentence = True
                                else:
                                    self.crc_fails += 1
                            except ValueError:
                                pass  # CRC Value was deformed and could not have been correct

                # Update CRC
                if self.process_crc:
                    self.crc_xor ^= ascii_char

                # If a Valid Sentence Was received and it's a supported sentence, then parse it!!
                if valid_sentence:
                    self.clean_sentences += 1  # Increment clean sentences received
                    self.sentence_active = False  # Clear Active Processing Flag

                    self.talker, message = self.gps_segments[0][:2], self.gps_segments[0][2:]
                    self.talker = self.talker_aliases.get(self.talker,
                                                          self.talker)

                    if message in self.supported_sentences \
                       and self.talker in self.talkers:

                        # parse the Sentence Based on the message type, return True if parse is clean
                        if self.supported_sentences[message](self):

                            # Let host know that the GPS object was updated by returning parsed sentence type
                            self.parsed_sentences += 1
                            return self.gps_segments[0]

                # Check that the sentence buffer isn't filling up with Garage waiting for the sentence to complete
                if self.char_count > self.SENTENCE_LIMIT:
                    self.sentence_active = False

        # Tell Host no new sentence was parsed
        return None

    def new_fix_time(self):
        """Updates a high resolution counter with current time when fix is updated. Currently only triggered from
        GGA, GSA and RMC sentences"""
        try:
            self.fix_time = utime.ticks_ms()
        except NameError:
            self.fix_time = time.time()

    #########################################
    # User Helper Functions
    # These functions make working with the GPS object data easier
    #########################################

    def satellite_data_updated(self):
        """
        Checks if the all the GSV sentences in a group have been read, making satellite data complete
        :return: boolean
        """
        if self.total_sv_sentences > 0 and self.total_sv_sentences == self.last_sv_sentence:
            return True
        else:
            return False

    def unset_satellite_data_updated(self):
        """
        Mark GSV sentences as read indicating the data has been used and future updates are fresh
        """
        self.last_sv_sentence = 0

    def satellites_visible(self):
        """
        Returns a dict of of the satellite PRNs currently visible to the receiver indexed by system and signal
        :return: dict
        """
        return {talker: tuple(sats) for talker, sats in self.satellite_data.items()}

    def time_since_fix(self):
        """Returns number of millisecond since the last sentence with a valid fix was parsed. Returns 0 if
        no fix has been found"""

        # Test if a Fix has been found
        if self.fix_time == 0:
            return -1

        # Try calculating fix time using utime; if not running MicroPython
        # time.time() returns a floating point value in secs
        try:
            current = utime.ticks_diff(utime.ticks_ms(), self.fix_time)
        except NameError:
            current = (time.time() - self.fix_time) * 1000  # ms

        return current

    def compass_direction(self):
        """
        Determine a cardinal or inter-cardinal direction based on current course.
        :return: string
        """
        # Calculate the offset for a rotated compass
        offset_course = (self.course + 11.25) % 360.0

        # Each compass point is separated by 22.5 degrees, divide to find lookup value
        dir_index = floor(offset_course / 22.5)

        final_dir = self.__DIRECTIONS[dir_index]

        return final_dir

    def latitude_string(self):
        """
        Create a readable string of the current latitude data
        :return: string
        """
        if self.coord_format == 'dd':
            formatted_latitude = self.latitude
            lat_string = str(formatted_latitude[0]) + '° ' + str(self._latitude[2])
        elif self.coord_format == 'dms':
            formatted_latitude = self.latitude
            lat_string = str(formatted_latitude[0]) + '° ' + str(formatted_latitude[1]) + "' " + str(formatted_latitude[2]) + '" ' + str(formatted_latitude[3])
        else:
            lat_string = str(self._latitude[0]) + '° ' + str(self._latitude[1]) + "' " + str(self._latitude[2])
        return lat_string

    def longitude_string(self):
        """
        Create a readable string of the current longitude data
        :return: string
        """
        if self.coord_format == 'dd':
            formatted_longitude = self.longitude
            lon_string = str(formatted_longitude[0]) + '° ' + str(self._longitude[2])
        elif self.coord_format == 'dms':
            formatted_longitude = self.longitude
            lon_string = str(formatted_longitude[0]) + '° ' + str(formatted_longitude[1]) + "' " + str(formatted_longitude[2]) + '" ' + str(formatted_longitude[3])
        else:
            lon_string = str(self._longitude[0]) + '° ' + str(self._longitude[1]) + "' " + str(self._longitude[2])
        return lon_string

    def speed_string(self, unit='kph'):
        """
        Creates a readable string of the current speed data in one of three units
        :param unit: string of 'kph','mph, or 'knot'
        :return:
        """
        if unit == 'mph':
            speed_string = str(self.speed[1]) + ' mph'

        elif unit == 'knot':
            if self.speed[0] == 1:
                unit_str = ' knot'
            else:
                unit_str = ' knots'
            speed_string = str(self.speed[0]) + unit_str

        else:
            speed_string = str(self.speed[2]) + ' km/h'

        return speed_string

    def ordinal_number(self, value):
        # Determine Date Suffix
        last_digit = value % 10
        if (4 <= value <= 20) or last_digit >= 4:
            return f'{value}th'
        elif last_digit == 1:
            return f'{value}st'
        elif last_digit == 2:
            return f'{value}nd'
        elif last_digit == 3:
            return f'{value}rd'
        # Shouldn't get here
        raise ValueError('Invalid value supplied', value)

    def time_string(self, format_24hrs=True):
        """Return time as a string.

        :param format_24hrs boolean - Whether to use 24 hour clock or am/pm"""
        h, m, s = self.timestamp
        s = int(s)
        if format_24hrs:
            return f'{h:02d}:{m:02d}:{s:02d}'
        else:
            ampm = 'pm' if h >= 12 else 'am'
            h_12 = 12 if h in (0, 12) else h % 12
            return f'{h_12:02d}:{m:02d}:{s:02d} {ampm}'

    def date_string(self, formatting='s_mdy'):
        """
        Creates a readable string of the current date.
        Can select between long format: January 1st, 2014
        long DMY format (i.e. UK, military): 1 January 2014
        or three short formats:
        11/01/2014 (MM/DD/YYYY)
        01/11/2014 (DD/MM/YYYY)
        2014-01-11 (YYYY-MM-DD) (aka ISO format)
        :param formatting: string 's_mdy', 's_dmy', 'iso', 'l_dmy', or 'long'
        :return: date_string  string with long or short format date
        """

        day, month, year = self.date
        # Long Format January 1st, 2014
        if formatting == 'long':
            # Retrieve Month string from private set
            month_name = self.__MONTHS[month - 1]
            ordday = self.ordinal_number(day)

            date_string = f'{month_name} {ordday}, {year}'
        elif formatting == 'l_dmy':
            month_name = self.__MONTHS[month - 1]
            date_string = f'{day} {month_name} {year}'
        elif formatting == 'iso':
            date_string = f'{year:04d}-{month:02d}-{day:02d}'
        elif formatting == 's_dmy':
            date_string = f'{day:02d}/{month:02d}/{year:04d}'
        else:  # Default date format
            date_string = f'{month:02d}/{day:02d}/{year:04d}'

        return date_string

    # All the currently supported NMEA sentences
    supported_sentences = {'RMC': gprmc,
                           'GGA': gpgga,
                           'VTG': gpvtg,
                           'GSA': gpgsa,
                           'GSV': gpgsv,
                           'GLL': gpgll,
                           'ZDA': gpzda,
                           'GNS': gpgns,
                           }

    talker_aliases = {'BD': 'GB',
                      'PQ': 'GQ',
                      'QZ': 'GQ',
                      }

    talkers = ('GP', # Navstar GPS
               'GL', # GLONASS
               'GA', # Galileo
               'GB', # BeiDou
               'GI', # NavIC/IRNSS
               'GQ', # QZSS
               'GN', # Multiple GNSS
               )

    # Map from NMEA system IDs to preferred talker IDs
    nmea_system_ids = {0x1: 'GP',
                       0x2: 'GL',
                       0x3: 'GA',
                       0x4: 'GB',
                       0x5: 'GQ',
                       0x6: 'GI',
                       }


if __name__ == "__main__":
    pass
