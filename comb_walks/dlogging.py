r'''
    File for a enhanced use of the logging system in Sage

    In this file we include a enchanced version of the logging system we can
    find in Python (see :module:`logging`) focused on:

    * Writting the log on a common file
    * Nice visualization using tabulations on the messages
    * Provide functionality for measuring time on a function on the log

    AUTHORS:
        - Antonio Jimenez-Pastor (2020-04-30): initial version

    TODO:
        * Add EXAMPLES section
        
    This package is under the terms of GNU General Public License version 3.
'''

# ****************************************************************************
#  Copyright (C) 2020 Antonio Jimenez-Pastor <ajpastor@risc.uni-linz.ac.at>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#                  https://www.gnu.org/licenses/
# ****************************************************************************

from functools import wraps
from logging import Logger, StreamHandler, ERROR, WARNING, INFO
import logging
from logging.handlers import RotatingFileHandler
import time

## Session methods
def is_session():
    return dLogger._DLOGGER != None

def init_session(name, level=0, file=None):
    if(not is_session()):
        dLogger._DLOGGER = dLogger(name, file=file)

    dLogger._DLOGGER.setLevel(int(level))
    return dLogger._DLOGGER

def getLogger():
    return dLogger._DLOGGER

def close_session():
    if(is_session()):
        dLogger._DLOGGER.close()
        dLogger._DLOGGER = None


# Logging methods
def log(level, msg, *args, **kwds):
    if(is_session()): 
        dLogger._DLOGGER.log(level, msg, *args, **kwds)
    else:
        logging.log(level, msg, *args, **kwds)
def warning(msg, *args, **kwds):
    if(is_session()): 
        dLogger._DLOGGER.warning(msg, *args, **kwds)
    else:
        logging.warning(msg, *args, **kwds)
def info(msg, *args, **kwds):
    if(is_session()): 
        dLogger._DLOGGER.info(msg, *args, **kwds)
    else:
        logging.info(msg, *args, **kwds)
def error(msg, *args, **kwds):
    if(is_session()): 
        dLogger._DLOGGER.error(msg, *args, **kwds)
    else:
        logging.error(msg, *args, **kwds)
def critical(msg, *args, **kwds):
    if(is_session()): 
        dLogger._DLOGGER.critical(msg, *args, **kwds)
    else:
        logging.critical(msg, *args, **kwds)
def debug(msg, *args, **kwds):
    if(is_session()): 
        dLogger._DLOGGER.debug(msg, *args, **kwds)
    else:
        logging.debug(msg, *args, **kwds)
def exception(msg, *args, **kwds):
    if(is_session()): 
        dLogger._DLOGGER.exception(msg, *args, **kwds)
    else:
        logging.exception(msg, *args, **kwds)
def fatal(msg, *args, **kwds):
    if(is_session()): 
        dLogger._DLOGGER.fatal(msg, *args, **kwds)
    else:
        logging.fatal(msg, *args, **kwds)

def open_function(name):
    if(is_session()): dLogger._DLOGGER.open_function(name)
def close_function(name):
    if(is_session()): dLogger._DLOGGER.close_function(name)

def dLogFunction(func):
    r'''
        Decorator for wrapping methods with the dLogger

        This decorator allows the user tu use the decorator ``@dLogFunction`` for wrap all
        the functions that want to control the time using a dLogger.

        This will automatically increase the identation of the dLogger and check the
        initial and final time of the method.
    '''
    @wraps(func)
    def dLogged(*args, **kwds):
        open_function(func.__name__)
        try:
            output = func(*args, **kwds)
        except Exception as e:
            error("Function %s closed by an error: %s" %(func.__name__, e))
            close_function(func.__name__)
            raise e

        close_function(func.__name__)
        return output
    return dLogged

class dLogger(Logger):
    r'''
        Class for a specialized Logger

        This Logger is focused on indenting the messages and for having the times of execution
        controlled on the messages. This Logger can dump its messages on a file. If the file
        is not provided, the standard output is used.

        INPUT:
            * ``name`: the identifier of the Logger.
            * ``level``: the threshold for printing the messages of the Logger.
            * ``file``: the name of the file to print the output. If there is none, we will use
              the standard output.
    '''
    _DLOGGER = None

    def __init__(self, name, level=0, file=None):
        import sys

        super(dLogger, self).__init__(name, level)
        self.__name = name

        self.addHandler(StreamHandler(sys.stdout))
        if(file != None):
            self.addHandler(RotatingFileHandler(file,"w"))

        self.__depth = 0
        self.__init_times = [time.time()]

        self.__calls = {}
        self.__stats = None

    def close(self):
        self.collect_stats()
        self.print_stats()

    def _log(self, level, msg, args, exc_info=None, extra=None, stack_info=False):
        # Adding the level
        if(level == ERROR): result_msg = "ERROR     :"
        elif(level == INFO): result_msg = "INFO      :"
        elif(level == WARNING): result_msg = "WARNING   :"
        else: result_msg = "Level (%02d):" %level

        # Adding the logger name
        result_msg += self.__name + ":"

        # Adding time to msg
        result_msg += self.__format_time(time.time()-self.__init_times[0]) + ":"

        # Adding the identation
        result_msg += ":".join(self.__depth*["**--"])
        if(self.__depth > 0): result_msg += ":"

        # Adding the message
        result_msg += msg

        super(dLogger, self)._log(level, result_msg, args, exc_info, extra, stack_info)

    def open_function(self, name):
        self.info("Starting function %s" %name)
        self.__init_times += [time.time()]
        self.__depth += 1

    def close_function(self, name):
        self.__depth = max(self.__depth-1, 0)
        total_time = time.time()-self.__init_times.pop(-1)
        self.info("Finishing function %s. Total time: %s" %(name, self.__format_time(total_time)))
        if(not name in self.__calls):
            self.__calls[name] = []
        self.__calls[name] += [total_time]

    def collect_stats(self):
        self.__stats = {func : (len(self.__calls[func]), max(self.__calls[func]), min(self.__calls[func]), (sum(self.__calls[func])/len(self.__calls[func]))) for func in self.__calls}

    def print_stats(self):

        max_name = max(len(func) for func in self.__stats)

        super(dLogger, self)._log(self.level, "STATISTICS OF METHODS CALLED DURING THIS LOGGER EXECUTION", ())
        line_row = max_name*"-" + "-+-" + 6*"-" + "-+-" + 9*"-" + "-+-" + 9*"-" + "-+-" + + 9*"-" + "--"
        super(dLogger, self)._log(self.level, line_row, ())
        title_row = "method".rjust(max_name) + " | " + "ncalls".rjust(6) + " | " + " max time" + " | " + " min time" + " | " + " avg time" + "  "
        super(dLogger, self)._log(self.level, title_row, ())
        super(dLogger, self)._log(self.level, line_row, ())
        super(dLogger, self)._log(self.level, line_row, ())
        for func in self.__stats:
            stat = self.__stats[func]
            row = func.rjust(max_name) + " | " + ("%d" %(stat[0])).rjust(6) + " | " + ("%.04f" %(stat[1])).rjust(9) + " | " + ("%.04f" %(stat[2])).rjust(9) + " | " + ("%.04f" %(stat[3])).rjust(9) + "  "
            super(dLogger, self)._log(self.level, row, ())
        super(dLogger, self)._log(self.level, line_row, ())

    def __format_time(self, time):
        return ("%04.04f" %time).rjust(9, '0')

