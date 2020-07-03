r'''
    File containing the exceptions of the package ``comb_walks``.

    In this file we define and describe all the exceptions that are particular
    for the package ``comb_walks``. This allow the user (and the package itself) 
    to a better description and recognition of errors while using the package

    AUTHORS:
        - Antonio Jimenez-Pastor (2020-07-03): initial version
        
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

## Error of type of model
class NonEllipticError(TypeError):
    r'''
        Type error for showing a model is not elliptic
    '''
    pass

## Error computing Weierstrass Normal Forms
class WeierstrassFormError(Exception):
    r'''
        This exception means that some error happend during the computation
        of a Weiertrass Normal Form for some curve.
    '''
    pass

class NoMapleError(WeierstrassFormError):
    r'''
        A class showing that the Maple interface is not working
    '''
    def __init__(self):
        super().__init__("NoMapleError: the Maple interface is not working")

class AlgWError(WeierstrassFormError):
    r'''
        A class showing that an error with algebraic numbers happend
        in the computation of a Weiertrass Normal Form.
    '''
    def __init(self):
        super().__init__("AlgWError: an error with algebraic numbers")