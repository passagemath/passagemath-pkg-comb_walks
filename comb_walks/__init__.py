r"""
    Package comb_walks

    In this package the user may find the following subpackages:
        * ``algeo``: some generic methods about Algebric Geometry
        * ``walkmodel``: the main structure for Walks in the Quarter Plane
        * ``get_data``: some specific methods for getting data from the Walk Models.
        * ``dlogging``: an extension of Loggers in python for our package.

    AUTHORS:
        - Antonio Jimenez-Pastor (2020-03-11): initial version
        
    This package is under the terms of GNU General Public License version 3.
"""

# ****************************************************************************
#  Copyright (C) 2020 Antonio Jimenez-Pastor <ajpastor@risc.uni-linz.ac.at>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#                  https://www.gnu.org/licenses/
# ****************************************************************************

from .alggeo import *
from .walkmodel import *
from .get_data import *
