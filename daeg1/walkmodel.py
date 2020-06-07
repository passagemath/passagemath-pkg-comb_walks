r'''
    File for the code for models of Walking in the quarter plane.

    This method includes a generic class and a bunch of preset variables
    that can be used to work with the generating functions of Walks on the
    quarter plane.

    In particular, lots of this methods works with the algebraic curve that
    the kernel polynomial defines for each model.

    AUTHORS:
        - Antonio Jimenez-Pastor (2019-06-12): initial version

    TODO:
        * Add EXAMPLES section
        
    This package is under the terms of GNU General Public License version 3.
'''

# ****************************************************************************
#  Copyright (C) 2019 Antonio Jimenez-Pastor <ajpastor@risc.uni-linz.ac.at>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#                  https://www.gnu.org/licenses/
# ****************************************************************************

# Sage imports
from sage.all import (ProjectiveSpace, QQ, ZZ, random, ceil, cached_method, parent,
    Hom, binomial, FractionField, vector, Matrix, Poset, DiGraph, Infinity,
    PolynomialRing, gcd, Integer, randint)
from sage.structure.coerce_exceptions import CoercionException

# Local imports
from .alggeo import (apply_map, zeros_bihom, point_extension, simpl_morphism, 
    simplify_rational_variety, pullback, asymptotics, polar_part, expand_at_point,
    order_morphism)
from . import dlogging
from .dlogging import dLogFunction


## Exception classes
class NonEllipticError(TypeError):
    r'''
        Type error for showing a model is not elliptic
    '''
    pass

class WalkModel():
    r'''
        Class for representing a model of walks on the quarter plane.

        A walk on the plane is a sequence of points `(P_0, P_1, \ldots) \in \mathbb{Z}^\mathbb{N}`
        where, we say:

        * `P_0` is the origin of the walk.
        * If the sequence is finite, the last point `P_n` is the *destiny* and `n` is the *length*.
        * The `i`th step is the difference `P_{i} - P_{i-1}`.

        Given a set `S \subset \mathbb{Z}`, we can define a model of walks on the plane using the
        elements of `S` as valid steps. This means that the model allows finite walks where the steps
        of the walk are contained in `S`.

        In particular, models of this type have been widely studied when `S \subset \{-1,0,1\}^2 \setminus \{(0,0)\}`,
        what are called *small steps*. Moreover, people is interested in the walks restricted to the quarter
        plane, i.e., all the points that are touched by a walk are in `\mathbb{N}^2`.

        Given a model, we can define the following generating function:

        .. MATH::

            Q(x,y,t) = \sum_{i,j,n \geq 0} q_{i,j,n} x^iy^jt^n,

        where `q_{i,j,n}` is the number of walks of length `n` that has origin at `(0,0)`
        and destiny `(i,j)` included in the model. This class provides several methods to understand this
        generating function.

        To initialize a model, the step set `S` needs to be provided. For doing so, a list of valid steps have to
        be given by the user:

        * A valid step is any list of tuple with more than 1 element.
        * The first two elements will be the coordinates of the step.
        * If a third element is given, it will be the weight for that step. The default weight is `1`.
        * If the list or tuple are longer, the other elements will be ignored.

        If a invalid step is given, a Warning will pop up in the context of the warning system
        provided by the Python package "logging". But the model will still be created without raising
        any error.
    '''
    ##########################################################################################
    ## STATIC ELEMENTS FOR ALL WALK MODELS
    ##########################################################################################
    _F = FractionField(PolynomialRing(QQ,['t'])); _t = _F.gens()[0]
    _XYZSpace = ProjectiveSpace(2,_F, 'xyz')
    _PxPySpace = ProjectiveSpace(1,_F,'x').cartesian_product(ProjectiveSpace(1,_F,'y'))
    _UVWSpace = ProjectiveSpace(2, _F, 'uvw')
    N = (0,1); NE = (1,1); E = (1,0); SE = (1,-1)
    S = (0,-1);SW = (-1,-1); W = (-1,0); NW = (-1,1)
    small_steps = [N, NE, E, SE, S, SW, W, NW]

    @staticmethod
    def model(model):
        r'''
            Static method for standarizing the input for deciding the model.

            There are a total of three models available:

            * The basic model, with coordinates `x`, `y`, `z`: 1, "xyz", "xy", "a", "A"
            * The Weierstrass model, with coordinates `u`, `v`, `w` (if the curve is elliptic): 2, "uvw", "uv", "w", "weierstrass", "W"
            * The doubly-projectivized model: when we projectivize `x` and `y` indepently: 3, "x0x1y0y1", "x0y0", "p", "projective", "P"

            EXAMPLES::

                sage: from daeg1.walkmodel import *
                sage: all(WalkModel.model(el) == "A" for el in [1,'xyz','xy','a','A'])
                True
                sage: all(WalkModel.model(el) == "W" for el in [2, 'uvw', 'uv', 'w', 'weierstrass', 'W'])
                True
                sage: all(WalkModel.model(el) == "P" for el in [3, 'x0x1y0y1', 'x0y0', 'p', 'projective', 'P'])
                True
                sage: WalkModel.model("mymodel")
                Traceback (most recent call last):
                ...
                ValueError: Model not recognized
        '''
        if(model == 1 or model == 'xyz' or model == 'xy' or model == 'a' or model == 'A'):
            return "A"
        elif(model == 2 or model == 'uvw' or model == 'uv' or model == 'w' or model == 'weierstrass' or model == "W"):
            return "W"
        elif(model == 3 or model == 'x0x1y0y1' or model == 'x0y0' or model == 'p' or model == 'projective' or model == "P"):
            return "P"

        raise ValueError("Model not recognized")

    @staticmethod
    def example_model():
        r'''
            Static method for getting an example of WalkModel used for several tests.

            The model returned is always the same (equivalent to ``RookModel``) with four steps
            (east, north, west and south) and the name ``Example Model``.

            EXAMPLE::

                sage: from daeg1.walkmodel import WalkModel
                sage: WalkModel.example_model()
                Walk Model (Example Model)
                sage: WalkModel.example_model().steps()
                [((1, 0), 1), ((0, 1), 1), ((-1, 0), 1), ((0, -1), 1)]
        '''
        return WalkModel((1,0), (0,1), (-1,0), (0,-1), name="Example Model")

    @staticmethod
    def random_model(max_value=100, frac_value=True, max_steps=8):
        r'''
            Method to get a random probabilistic model

            This method generates a list of probabilities for taking each of the steps using
            the method :func:`~sage.misc.prandom.randint` up to the value given as an argument.

            INPUT:
                * ``max_value``: the maximal proportion between probabilities. Must be an
                  integer (by default ``100``).
                * ``frac_value``: boolean argument (``True`` by default) that decides wheher store
                  the weights of the steps as probabilities (i.e., elements between 0 and 1) or as
                  integers. 
                * ``max_steps``: maximal number of different steps allowed in the model. This 
                  guarantees that this numbers of steps will be considered although if the random
                  generator creates a zero weight, then this step will not be included. This value
                  is by default `8`.

            EXAMPLE::

                sage: from daeg1 import *
                sage: WalkModel.random_model()
                Walk Model with steps: ...)
                sage: WalkModel.random_model(max_steps=4).nsteps() <= 4
                True
        '''
        ## Considering the argument `max_steps`
        try:
            max_steps = int(max_steps) # Trying to cast it to a integer
        except: # If any error occurs, we set it to the default (8)
            max_steps = 8
        # If a valid entry between 0 and 8 is selected we select some random elements
        if(max_steps < 8 and max_steps):
            from sage.combinat.permutation import Permutations
            p = Permutations(8).random_element()
            steps = [WalkModel.small_steps[p.index(i)] for i in range(1,max_steps+1)]
        else: # If the input is not an appropriate integer we get all the steps
            steps = WalkModel.small_steps
            max_steps = 8

        probabilities = [Integer(randint(0, max_value)) for _ in range(max_steps)]
        sum_prob = sum(probabilities)

        if(frac_value): probabilities = [el/sum_prob for el in probabilities]

        return WalkModel(*[(steps[i][0], steps[i][1], probabilities[i]) for i in range(len(probabilities))])



    ##########################################################################################
    ## CONCRETE METHODS FOR EACH OBJECT
    ##########################################################################################
    def __init__(self, *args, **kwds):
        ## Declaring variables for future computations
        # Variables for ambient spaces
        self.__F = WalkModel._F
        self.__XYZSpace = WalkModel._XYZSpace
        self.__PxPySpace = WalkModel._PxPySpace
        self.__UVWSpace = WalkModel._UVWSpace

        # Variables for the algebraic elements
        self.__kernel = {} # Variable for the kernel functions
        self.__curve = {} # Variable for the curves
        self.__neutral = {} # Variable for the neutral points
        self.__maps = {} # Variable for the mapping between the curves
        self.__A = {} # Variable for the splitting of the kernel in terms of y (keys are (model,i))
        self.__B = {} # Variable for the splitting of the kernel in terms of x (keys are (model,i))
        self.__discriminant = {} # Variable for the discriminants for the krnel function (keys are (model, i))

        self.__maple = {} # Variable for saving the data got from Maple

        # Variables for KR methods
        self.__KR_f = {}
        self.__KR_poles_f = {}

        # Variables for mappings
        self.__i = {} # Variable for saving the involutions
        self.__b = {} # Variable for saving the b functions

        # Variables for functional information
        self.__poles = {} # Variable for the poles computations
        self.__reductions = {} # Variable for the reduction computations
        self.__telescoper = {} # Variable for the telescoper computations

        # Variables for data of the model
        self.__steps = None # Variable to store the steps with their weights
        self.__cum_steps = None # Variable to order the steps (for create random walks)
        self.__cum_weights = None # Variable to accumulate weights (for create random walks)

        # Variables for the algebriac extensions
        self.__field_F = QQ # Variable for the extensions before the parameter `t`
        self.__field_G = self.__F # Variable for the extensions after the parameter `t`
        self.__nextensions = 0 # Number of extensions (for deciding the name)

        ## Reading the input
        ## Checking the input
        self.__name = kwds.get('name', None)
        ## If one argument is given is must be a list of pairs
        if(len(args) == 1):
            args = args[0]

        ## We check every element of the list args
        self.__steps = {}
        for el in args:
            if(not (isinstance(el, list) or isinstance(el, tuple))):
                dlogging.error("WalkModel.__init__: Invalid argument %s --> expected list or tuple" %(str(el)))
                raise TypeError("Invalid argument %s --> expected list or tuple" %(str(el)))
            elif(len(el) < 2):
                dlogging.error("WalkModel.__init__: Invalid argument %s --> too short element" %(str(el)))
                raise ValueError("Invalid argument %s --> too short element" %(str(el)))
            else:
                if(len(el) > 3):
                    dlogging.error("WalkModel.__init__: Data lost %s --> too long element, just taking the first three" %(str(el)))
                    raise ValueError("Invalid argument %s --> too long element, just taking the first three" %(str(el)))
                new_step = tuple([ZZ(el[0]), ZZ(el[1])])
                new_weight = 1
                if(len(el)>2):
                    new_weight = QQ(el[2])
                if(new_weight == 0):
                    dlogging.info("WalkModel.__init__: given weight is 0 --> ignoring the step %s" %(str(el)))
                elif(new_step in self.__steps):
                    dlogging.info("WalkModel.__init__: Repeated step %s --> step already given, ignoring the new" %(str(el)))
                else:
                    self.__steps[new_step] = new_weight
        if(len(self.__steps) == 0):
            raise TypeError("No valid argument was given to the model. Impossible to create the model")
        ## Normalizing weights: making weights rational numbers between 0 and 1
        sum_of_weights = sum(self.__steps.values())
        normalized_steps = {step : QQ(self.__steps[step])/sum_of_weights for step in self.__steps}

        ## Generating the binary line of weights
        it = list(normalized_steps.keys())
        if(len(it) > 0):
            step = it[0]
            self.__cum_steps = [step]
            self.__cum_weights = [normalized_steps[step]]
            for step in it[1:]:
                self.__cum_weights += [self.__cum_weights[-1]+normalized_steps[step]]
                self.__cum_steps += [step]

    ##########################################################################################
    ## Geometric methods
    def base_ring(self):
        r'''
            Method to get the current base ring of the Walk Model.

            This method returns the current *coefficient ring* where all the ambient spaces
            are based (see method :func:`ambient` for further information)

            **Remark**: this method will return a new element if we find a needed algebraic extension.
            Hence, the use of this method instead of a variable is highly recommended.
        '''
        return self.__F

    def change_ring(self, new_ring):
        r'''
            Method to change the base ring of the model.

            This method changes the base ring of the model (see method :func:`base_ring` for further information)
            and it ensures that all the data that have been already computed using the previous ring is valid for
            this new base ring.

            This requires that the pushout between the current ring and the new ring is exactly the new ring.
            Otherwise an error will be raised.

            INPUT:
                * ``new_ring``: the new base ring for all the elements of the model. This must be an extension
                  of the current ring (see method :func:`base_ring`).

            EXAMPLES::

                sage: from daeg1.walkmodel import WalkModel; m = WalkModel.example_model()
                sage: t = m.pars(); F = m.base_ring()
                sage: nF = FractionField(NumberField(QQ['i']('i^2+1'), 'i')[t])
                sage: m.ring(1) # Basic ring
                Multivariate Polynomial Ring in x, y, z over Fraction Field of Univariate Polynomial Ring in t over Rational Field
                sage: m.change_ring(F) # Do nothing
                sage: m.ring(1)
                Multivariate Polynomial Ring in x, y, z over Fraction Field of Univariate Polynomial Ring in t over Rational Field
                sage: m.change_ring(nF.base()) # Error because nF.base() is not a field
                Traceback (most recent call last):
                ...
                CoercionException: The new ring (...) is not a super ring for the current ring (...)
                sage: m.change_ring(Integer(10)) # Error because 10 is not a ring
                Traceback (most recent call last):
                ...
                CoercionException: The argument (10) is not valid for pushout
                    Reason: ...
                sage: m.change_ring(nF) # Successfull change
                sage: m.ring(1)
                Multivariate Polynomial Ring in x, y, z over Fraction Field of Univariate Polynomial Ring in t over Number Field in i with defining polynomial i^2 + 1
        '''
        from sage.categories.pushout import pushout

        ## Checking the new ring
        try:
            if(pushout(self.base_ring(), new_ring) != new_ring):
                raise CoercionException("The new ring (%s) is not a super ring for the current ring (%s)" %(new_ring, self.base_ring()))
        except AttributeError as e:
            raise CoercionException("The argument (%s) is not valid for pushout\n\tReason: %s" %(new_ring, e))

        if(new_ring != self.base_ring()):
            ## Updating the variables
            self.__F = new_ring
            self.__XYZSpace = self.ambient(1).change_ring(new_ring)
            self.__UVWSpace = self.ambient(2).change_ring(new_ring)
            self.__PxPySpace = self.ambient(3).change_ring(new_ring)

            for model in self.__kernel:
                self.__kernel[model] = self.ring(model)(self.__kernel[model])
            for model in self.__curve:
                self.__curve[model] = self.__curve[model].change_ring(new_ring)
            for model in self.__neutral:
                self.__neutral[model] = self.__neutral[model].change_ring(new_ring)
            for key in self.__maps:
                self.__maps[key] = self.__maps[key].change_ring(new_ring)

            for key in self.__A:
                self.__A[key] = self.__A[key].change_ring(new_ring)
            for key in self.__B:
                self.__B[key] = self.__B[key].change_ring(new_ring)
            for key in self.__discriminant:
                self.__discriminant[key] = self.__discriminant[key].change_ring(new_ring)

            for key in self.__i:
                self.__i[key] = self.__i[key].change_ring(new_ring)
            for key in self.__B:
                self.__b[key] = self.__b[key].change_ring(new_ring)

            for key in self.__poles:
                self.__poles[key] = [el.change_ring(new_ring) for el in self.__poles[key]]

            ## Some cached variables are too complicated to cast. We clean those
            self.__recutions = {} # Clean reductions (we redo operations)
            self.__telescoper = {} # Clean telescoper (we redo operations)

    def ambient(self, model):
        r'''
            Method to get the current ambient space of the curve depending on the model required.

            Since there are three different models, we have three different ambient spaces:

            * For model "A": the space `P^2` with coordinates `(x:y:z)`.
            * For model "W": the space `P^2` with coordinates `(u:v:w)`.
            * For model "P": the space `P^1\times P^1` with two projective coordinates `(x0:x1,y0:y1)`

            **Remark**: this method will return a new element if we find a needed algebraic extension.
            Hence, the use of this method instead of a variable is highly recommended.

            INPUT:
                * ``model``: the type of ambient space we look. See method :func:`model` for further information.

            EXAMPLES::

                sage: from daeg1.walkmodel import WalkModel; m = WalkModel.example_model()
                sage: m.ambient(1)
                Projective Space of dimension 2 over Fraction Field of Univariate Polynomial Ring in t over Rational Field
                sage: m.ambient(2)
                Projective Space of dimension 2 over Fraction Field of Univariate Polynomial Ring in t over Rational Field
                sage: m.ambient(3)
                Product of projective spaces P^1 x P^1 over Fraction Field of Univariate Polynomial Ring in t over Rational Field
                sage: m.ambient(1).gens()
                (x, y, z)
                sage: m.ambient(2).gens()
                (u, v, w)
                sage: m.ambient(3).gens()
                (x0, x1, y0, y1)
                sage: all(m.ambient(el) == m.ambient(1) for el in [1,'xyz','xy','a','A'])
                True
                sage: all(m.ambient(el) == m.ambient(2) for el in [2, 'uvw', 'uv', 'w', 'weierstrass', 'W'])
                True
                sage: all(m.ambient(el) == m.ambient(3) for el in [3, 'x0x1y0y1', 'x0y0', 'p', 'projective', 'P'])
                True
        '''
        model = self.model(model)
        if(model == "A"):
            return self.__XYZSpace
        elif(model == "W"):
            return self.__UVWSpace
        elif(model == "P"):
            return self.__PxPySpace

    def ring(self,model):
        r'''
            Method to get the current coordinate ring of the ambient space of the curve depending on the model required.

            Since there are three different models, we have three different ambient spaces:
                * For model ``A``: polynomial ring in `x`, `y`, `z` over `Q(t)`.
                * For model ``W``: polynomial ring in `u`, `v`, `w` over `Q(t)`.
                * For model ``P``: polynomial ring in `x_0`, `x_1`, `y_0`, `y_1` over `Q(t)`.

            REMARK: 
                * This method will return a new element if we find a needed algebraic extension.
                  Hence, the use of this method instead of a variable is highly recommended.

            INPUT:
                * ``model``: the type of ambient space we look. See method :func:`model` for further information.

            EXAMPLES::

                sage: from daeg1.walkmodel import WalkModel; m = WalkModel.example_model()
                sage: x,y,z = m.vars(1); u,v,w = m.vars(2); x0,x1,y0,y1 = m.vars(3); t = m.pars()
                sage: all(m.ring(el) == m.base_ring()[x,y,z] for el in [1,'xyz','xy','a','A'])
                True
                sage: all(m.ring(el) == m.base_ring()[u,v,w] for el in [2, 'uvw', 'uv', 'w', 'weierstrass', 'W'])
                True
                sage: all(m.ring(el) == m.base_ring()[x0,x1,y0,y1] for el in [3, 'x0x1y0y1', 'x0y0', 'p', 'projective', 'P'])
                True

            These relation between the :func:`base_ring` and the coordinate rings has to be preserved even
            after changing the base ring (see method :func:`change_ring`)::

                sage: nF = FractionField(NumberField(QQ['i']('i^2+1'), 'i')[t])
                sage: m.change_ring(nF)
                sage: all(m.ring(el) == m.base_ring()[x,y,z] for el in [1,'xyz','xy','a','A'])
                True
                sage: all(m.ring(el) == m.base_ring()[u,v,w] for el in [2, 'uvw', 'uv', 'w', 'weierstrass', 'W'])
                True
                sage: all(m.ring(el) == m.base_ring()[x0,x1,y0,y1] for el in [3, 'x0x1y0y1', 'x0y0', 'p', 'projective', 'P'])
                True
        '''
        return self.ambient(model).coordinate_ring()

    def vars(self, model):
        r'''
            Method to retrieve the current variables employed in one particular model of the curve.

            **Remark**: this method will return a new element if we find a needed algebraic extension.
            Hence, the use of this method instead of a variable is highly recommended.

            INPUT:
                * ``model``: the type of ambient space we look. See method :func:`model` for further information.

            EXAMPLES::

                sage: from daeg1.walkmodel import WalkModel; m = WalkModel.example_model()
                sage: all(str(m.vars(el)) == "(x, y, z)" for el in [1,'xyz','xy','a','A'])
                True
                sage: all(str(m.vars(el)) == "(u, v, w)" for el in [2, 'uvw', 'uv', 'w', 'weierstrass', 'W'])
                True
                sage: all(str(m.vars(el)) == "(x0, x1, y0, y1)" for el in [3, 'x0x1y0y1', 'x0y0', 'p', 'projective', 'P'])
                True
        '''
        return self.ring(model).gens()

    def pars(self):
        r'''
            Method to get the parameters of the ambient space (namely `t`).

            This method returns all the parameters that we can find in the coefficients field of the
            WalkModel. See method :func:`base_ring` for further information.

            EXAMPLE:

                sage: from daeg1.walkmodel import WalkModel; m = WalkModel.example_model()
                sage: m.pars()
                t

            All the models in the list have only one parameter::

                sage: from daeg1.walkmodel import AllModels
                sage: all(m.pars() == other.pars() for other in AllModels)
                True
        '''
        parameters = self.base_ring().gens()
        if(len(parameters) == 1):
            return parameters[0]
        return parameters

    ##########################################################################################
    ## Probability and random methods
    def random_step(self):
        '''
            Method to get a valid step from the model.

            This method computes a random step contained in the step set of the model. The probability
            distribution is proportional to the weight of the steps, i.e., if a step `s_1` has weight
            `1` and another step `s_2` has weight `2`, then `s_2` has *double* probability of being chosen.

            EXAMPLES::

                sage: from daeg1.walkmodel import *
                sage: m = WalkModel(N,S,E)
                sage: all(m.random_step() in (N,S,E) for i in range(10))
                True
                sage: m = WalkModel([0,1], [0,2])
                sage: all(m.random_step() in ((0,1),(0,2)) for i in range(10))
                True
        '''
        # Getting a random value between 0 and 1
        r = random()

        # Looking for the appropiate step
        ## Using a binary search proccess to find the index corresponding to the
        ## valid step.
        min = 0; max = self.nsteps()
        while(max - min > 1):
            next = ceil((min+max)/2)
            if(r == self.__cum_weights[next-1]):
                return self.__cum_steps[next]
            elif(r < self.__cum_weights[next-1]):
                max = next
            else:
                min = next
        return self.__cum_steps[min]

    def random_walk(self, size, start=(0,0), steps=False, restriction="quarter"):
        '''
            Method to create a random walk valid for the model.

            This method allows the user to create a random walk using the steps from the model
            and where the probability distribution of the steps is propostional to their weights.

            Further restrictions can be applied like:

            * The starting point: see argument ``start``.
            * The space where the walk con go trhough: see argument ``restriction``.

            INPUT:
                * ``size``: the length of the walk that will be generated. If at some point we reach a coordinate where
                  no further steps can be applied, then we return the shorter walk.
                * ``start``: coordinates of the starting point of the walk.
                * ``steps``: a boolean argument to determine if the output will include all the intermidiate steps
                  through the walk or (if ``False``) only returns the destiny.
                * ``restriction``: restriction of the walk. There are three possible choices:
                    - ``"quarter"``: the walk will be in the first quadrant.
                    - ``"half"``: the walk will be in the upper half plane.
                    - anything else: the walk is free to move through the whole plane.
        '''
        all_steps = []
        final_point = start
        for i in range(size):
            ## Checking possible steps
            valid_steps = []
            for step in self.__steps:
                if(restriction == "quarter"):
                    if(all(final_point[i] + step[i] >= 0 for i in range(2))):
                        valid_steps += [step]
                elif(restriction == "half"):
                    if(final_point[1] + step[1] >= 0):
                        valid_steps += [step]
                else:
                    valid_steps += [step]
            if(len(valid_steps) < 1):
                dlogging.warning("WalkModel.random_walk: not possible to continue this walk at position %s after %d steps" %(str(final_point),i))
                break
            elif(len(valid_steps) == 1):
                next_step = valid_steps[0]
            else:
                next_step = self.random_step()
                while(not(next_step in valid_steps)):
                    next_step = self.random_step()

            final_point = tuple([final_point[i] + next_step[i] for i in range(2)])
            all_steps += [next_step]

        if(steps):
            return final_point, all_steps
        return final_point

    @cached_method
    def weight_matrix(self):
        r'''
            Method to get the probability matrix for this model.

            This method (only working right now for models with small steps) follows the definitions
            on the book by Fayolle et al. This books propose to study a matrix generated by the 
            probabilities of jumping to the new position.

            Since this probability is marked by the weights of the steps, we construct an equivalent
            matrix using these weights:

            .. MATH::

                \left(\begin{array}{ccc}
                    w_{-1,1} & w_{0,1} & w_{1,1}\\
                    w_{-1,0} & w_{0,0}-S & w_{1,0}\\
                    w_{-1,-1} & w_{0,-1} & w_{1,-1}
                \end{array}\right)

            where `S` is the sum of all weights.

            EXAMPLES::

                sage: from daeg1 import *
                sage: m = RookModel; m.weight_matrix()
                [ 0  1  0]
                [ 1 -4  1]
                [ 0  1  0]
                sage: m = KingModel; m.weight_matrix()
                [ 1  1  1]
                [ 1 -8  1]
                [ 1  1  1]
                sage: m = WalkModel((2,1,1), N, S, E); m.weight_matrix()
                Traceback (most recent call last):
                ...
                TypeError: The model is not of short steps
                sage: m = WalkModel(N,S,E,W,(0,0,Integer(1)/2)); m.weight_matrix()
                [ 0  1  0]
                [ 1 -4  1]
                [ 0  1  0]

            Using Lemma 4.1.1 from Fayolle's book, we have that the order of `\tau` is `2` if 
            and only if the determinant of this matrix is exactly zero::

                sage: all(dic_models["FG-BMM-1.%02d" %i].weight_matrix().determinant() == 0 for i in range(1,11))
                True
        '''
        if(not self.is_short_walk()):
            raise TypeError("The model is not of short steps")
        S = sum(step[1] for step in self.steps())

        return Matrix([
            [self.weight(WalkModel.NW), self.weight(WalkModel.N), self.weight(WalkModel.NE)],
            [self.weight(WalkModel.W), self.weight((0,0)) - S, self.weight(WalkModel.E)],
            [self.weight(WalkModel.SW), self.weight(WalkModel.S), self.weight(WalkModel.SE)]])

    @cached_method
    def weight_minor_matrix(self):
        r'''
            Method to get the matrix of minors of the weight matrix

            This method comptues the matrix composed by minors from the weight matrix
            (see method :func:`weight_matrix`) in such an order that fits equation
            (4.1.6) from Fayolle's book.

            .. MATH::

                \begin{pmatrix}
                    \Delta_{2,3} & \Delta_{3,3} & \Delta_{2,2} & \Delta_{3,2}\\
                    \Delta_{1,3} & -\Delta_{2,3} & \Delta_{1,2} & -\Delta_{2,2}\\
                    \Delta_{2,2} & \Delta_{3,2} & \Delta_{2,1} & \Delta_{3,1}\\
                    \Delta_{1,2} & -\Delta_{2,2} & \Delta_{1,1} & -\Delta_{2,1}
                \end{pmatrix},

            where `\Delta_{i,j}` is the 2-minor from the weight matrix after removing
            the `i`th row and the `j`th column.

            EXAMPLE::

                sage: from daeg1 import *
                sage: m = dic_models["FG-BMM-1.02"]
                sage: m.weight_minor_matrix()
                [ 0 -4  0  0]
                [ 4  0  0  0]
                [ 0  0  0  4]
                [ 0  0 -4  0]
                sage: m.weight_minor_matrix().determinant()
                256

            The determinant of this matrix indicates if the map `\tau` has order 3::

                sage: sage: all(dic_models["FG-BMM-2.%d" %i].weight_minor_matrix().determinant() == 0 for i in range(1,6))
        '''

        M = self.weight_matrix()
        minor = lambda i,j : Matrix([[M[a][b] for b in range(M.ncols()) if b != (j-1)] for a in range(M.nrows()) if a != (i-1)]).determinant()

        return Matrix([
            [minor(2,3),  minor(3,3), minor(2,2),  minor(3,2)],
            [minor(1,3), -minor(2,3), minor(1,2), -minor(2,2)],
            [minor(2,2),  minor(3,2), minor(2,1),  minor(3,1)],
            [minor(1,2), -minor(2,2), minor(1,1), -minor(2,1)]
        ])

        


    ##########################################################################################
    ## Basic properties
    def steps(self):
        r'''
            Method that return the step set for this Walk Model

            This method returns a list with pairs `(s, w_s)` where `s` is a valid step
            for the model and `w_s` is the corresponding weight associated to `s`.

            EXAMPLES::

                sage: from daeg1.walkmodel import *
                sage: m = WalkModel(N,S, [1,1,3]); m.steps()
                [((0, 1), 1), ((0, -1), 1), ((1, 1), 3)]
                sage: m = WalkModel(NW,S, [2,3,1], [2,5,5]); m.steps()
                [((-1, 1), 1), ((0, -1), 1), ((2, 3), 1), ((2, 5), 5)]
        '''
        return list(self.__steps.items())

    def weight(self, step):
        r'''
            Method to get the weight associated with a particular step

            This method is a getter from the variable :func:`steps` which extracts the weight
            information of a particular step. If such step is not in the model, this method returns 0.

            INPUT:
                * ``step``: a step in a tuple format. This tuple will be casted into a tuple of ``Integer``,
                  in order to use the equality of tuples to check whether the step is in the model or not.

            OUTPUT: 
                The value of the weight of the step in the walk. If the step is not present, then the returned
                value is zero.

            EXAMPLES::

                sage: from daeg1 import *
                sage: m = RookModel
                sage: all(m.weight(el) == 1 for el in [N,S,E,W])
                True
                sage: all(m.weight(el) == 0 for el in [NE, NW, SW, SE])
                True
                sage: m.weight((0,0))
                0
                sage: m = WalkModel(N,S,E,W,(0,0,Integer(1)/2))
                sage: all(m.weight(el) == 1 for el in [N,S,E,W])
                True
                sage: all(m.weight(el) == 0 for el in [NE, NW, SW, SE])
                True
                sage: m.weight((0,0))
                1/2
        '''
        try:
            step = (ZZ(step[0]), ZZ(step[1]))
        except Exception as e:
            raise TypeError("The step must be an iterable with at least 2 elements that can be casted into integers", e)

        return self.__steps.get(step, 0)

    @cached_method
    def nsteps(self):
        r'''
            Method to get the total number of steps of the model.

            This method returns the number of steps that are in the model. It is important
            to remark that we can not have repeated steps or that the weight does not
            change the counting of the steps.

            EXAMPLES::

                sage: from daeg1.walkmodel import *
                sage: m = WalkModel(N,S, [1,1,3]); m.nsteps()
                3
                sage: m = WalkModel(N,N,N,N,N); m.nsteps()
                1
                sage: m = WalkModel(N,NE,E,SE,S,SW,W,NW); m.nsteps()
                8
        '''
        return len(self.__steps)

    @cached_method
    def is_short_walk(self):
        r'''
            Method to check wether a model is of short steps or not.

            A step `s = (a,b)` is said to be *short* if `s \neq (0,0)` and `-1 \leq a,b \leq 1`.
            This method returns ``True`` if all the steps of the model are short and
            ``False`` otherwise.

            EXAMPLES::

                sage: from daeg1.walkmodel import *
                sage: m = WalkModel(N, S, [1,1,3]); m.is_short_walk()
                True
                sage: m = WalkModel(N, [2,1]); m.is_short_walk()
                False

            For all the examples considered in the papers of MBB and DHRS, they are of short steps::

                sage: all(m.is_short_walk() for m in AllModels)
                True
        '''
        return max(max(abs(step[i]) for step in self.__steps) for i in range(2)) == 1

    @cached_method
    def is_singular(self):
        r'''
            Method to check wether a model is *singular* or not.

            A model of walks in the quarter plane is called singular if, for all the steps
            `s = (a,b)` of the model we have `a+b \geq 0`. These models have the property
            that there are not walks on the quarter plane that comes back to the origin.

            EXAMPLES::

                sage: from daeg1.walkmodel import *
                sage: m = WalkModel(N,NW,NE,E,SE); m.is_singular()
                True
                sage: m = WalkModel([-2,2], [2, -2], N); m.is_singular()
                True
                sage: m = WalkModel([2,0], [2,1]); m.is_singular()
                True
                sage: m = WalkModel(N,S,E,W); m.is_singular()
                False

            For short walks, singular models are precisely those models which kernel equation
            generates a singular (i.e., non-elliptic) curve::

                sage: all(m in NonEllipticC for m in AllModels if m.is_singular())
                True

        '''
        return all(sum(step[i] for i in range(2))>=0 for step in self.__steps)

    @cached_method
    def is_weighted(self):
        r'''
            Method to check wether a model is weighted or not.

            We consider that a model is weighted if there are more than one value for the weight.
            This means that if all the steps have the same weight (even if such weight is not 1)
            the model is unweighted.

            EXAMPLES::

                sage: from daeg1.walkmodel import *
                sage: m = WalkModel(N,S,E,W); m.is_weighted()
                False
                sage: m = WalkModel(N,S, [1,1,2]); m.is_weighted()
                True
                sage: m = WalkModel([1,1,2], [0,1,2], [-1,1,2]); m.is_weighted()
                False

            All the models considered in the papers by BMM and DHRS are not weighted::

                sage: all(not m.is_weighted() for m in AllModels)
                True

        '''
        return len(set(self.__steps.values())) != 1

    @cached_method
    def get_unweighted_model(self):
        r'''
            Method that creates the unweighted equivalent model

            This method creates a new model for walks in the quarter plane where we remove all
            the weights and stablish them to 1.
        '''
        if(self.is_weighted()):
            return WalkModel(self.__steps.keys())
        return self

    ##########################################################################################
    ## Kernel and Step functions
    @cached_method
    def step(self):
        r'''
            Method that return the step Laurent polynomial associated with the Model.

            Given a model for walks, the step rational function is determined by the valid steps
            of the model. Let `(P_0,\ldots,P_n)` be a valid walk. This walk makes a contribution on
            the generating function depending on what is its destiny and what which steps it makes.

            In fact, each step `(s_x, s_y)` with weight `w` make a contribution of `wx^{s_x}y^{s_y}t`.
            In this way, we define the step rational function as the sum of all the possible contributions
            of the valid steps of the model.

            This rational function is always a Laurent polynomial, i.e., a rational function that
            can be polynomialy expressed in `x`, `y`, `1/x` and `1/y`.

            EXAMPLES::

                sage: from daeg1.walkmodel import *
                sage: m = WalkModel(N,E,S,W); m.step()
                (x^2*y + x*y^2 + x + y)/(x*y)
                sage: m.step() == (y + x + 1/y + 1/x)
                True
        '''
        x,y,_ = self.vars("A")

        p = sum(self.__steps[st]*x**st[0]*y**st[1] for st in self.__steps)

        return p

    def kernel(self, model="A"):
        r'''
            Method that returns the associated kernel function for a Model.

            In walks on the quarter plane, we can see that the step function (see
            method :func:`step`) allows to get a functional
            equation for the generating function `Q(x,y,t)`. Let `K(x,y,t) = xy(1-tS(x,y))`, then

            In the case of short steps, this kernel can be computed as

            .. MATH::

                K(x,y,t)Q(x,y,t) = K(0,y,t)Q(0,y,t) + K(x,0,t)Q(x,0,t) - K(0,0,t)Q(0,0,t)

            It is interesting to remark that, when the walks have short steps, `K(x,y,t)` is
            *a polynomial* in `x`, `y` and `t`, so the evaluation with `x=0` and `y=0` in the previous
            equation always make sense.

            This function `K(x,y,t)` is called the Kernel function for the model.

            This polynomial can be interpreted as a defining equation for a plane curve (see method
            :func:`curve`), and it may have several representations
            depending on how we embed this affine curve in `x` and `y` into a projective space:

            * For the model "A": the curve is embedded in `P^2`, using coordinates `x`, `y` and `z`.
            * For the model "P": the curve is embedded in `P^1\times P^1`, using two projective coordinates.
            * For the model "W": (**only** if the curve defined is elliptic) the curve is embedded in `P^2`
              and transformed into Weiertrass normal form.

            INPUT:
                * ``model``: it decides the kernel is returned (see method :func:`model`)


            EXAMPLES::

                sage: from daeg1.walkmodel import *
                sage: m = WalkModel(N,S,E,W); m.kernel()
                (-t)*x^2*y + (-t)*x*y^2 + x*y*z + (-t)*x*z^2 + (-t)*y*z^2
                sage: m.kernel('P')
                (-t)*x0*x1*y0^2 + (-t)*x0^2*y0*y1 + x0*x1*y0*y1 + (-t)*x1^2*y0*y1 + (-t)*x0*x1*y1^2
                sage: m.kernel('W')
                (-4)*u^3 + v^2*w + (4/3*t^4 - 4/3*t^2 + 1/12)*u*w^2 + (-8/27*t^6 - 5/9*t^4 + 1/9*t^2 - 1/216)*w^3
                sage: all(m.kernel(inp) is m.kernel('A') for inp in [1,'xyz','xy','a','A'])
                True
                sage: all(m.kernel(inp) is m.kernel('P') for inp in [3, 'x0x1y0y1', 'x0y0', 'p', 'projective', 'P'])
                True
                sage: all(m.kernel(inp) is m.kernel('W') for inp in [2, 'uvw', 'uv', 'w', 'weierstrass', 'W'])
                True

            For all the models in the papers of BMM and DHRS, we can check the identity with the definition::

                sage: all(m.kernel("A") == (x*y*(1-t*m.step()))(x=x/z, y=y/z).numerator() for m in AllModels) # long time
                True
                sage: all(m.kernel("P") == (x*y*(1-t*m.step()))(x=x0/x1, y=y0/y1).numerator() for m in AllModels) # long time
                True

            The Weierstras model can not be computed for some models since they are not elliptic::

                sage: m = NonEllipticC[0]; m.kernel('W')
                Traceback (most recent call last):
                ...
                NonEllipticError: The kernel is not a elliptic curve --> No Weierstrass model
        '''
        model = self.model(model)
        if(not (model in self.__kernel)):
            R = self.ring(model)
            t = self.pars()
            if(model == "A"):
                s = self.step()
                x,y,z = self.vars(model)

                k = R(x*y*(1 - s*t))
                self.__kernel[model] = k.homogenize(z)
            elif(model ==  "P"):
                k = self.kernel()
                x0,x1,y0,y1 = self.vars(model)

                self.__kernel[model] = k(z=1,x=x0/x1,y=y0/y1).numerator()
            elif(model == "W"):
                if(not self.is_elliptic()):
                    raise NonEllipticError("The kernel is not a elliptic curve --> No Weierstrass model")
                self.__get_maple_info()

        return self.__kernel[model]

    def curve(self, model="A"):
        r'''
            Method to get the algebraic curve defined by the kernel function.

            The kernel of a model (see :func:`kernel`) is a polynomial in the variables `x` and `y`.
            This polynomial can be seen as the defining polynomial of a curve on the plane. This method
            returns the Sage structure for that particular curve.

            Depending on how we homogenize the kernel function, we may end up with three different curves:
                * With model ``A``: we homogenize with one variable `z`.
                * With model ``P``: we homogenize with two variables `x \rightarrow x_0/x_1` and `y \rightarrow y_0/y_1`.
                * With model ``W``: if the curve is elliptic, this provides the Weierstrass normal form of the curve.

            INPUT:
                * ``model``: it decides the curve is returned (see method :func:`model`)

            EXAMPLES::

                sage: from daeg1.walkmodel import *
                sage: m = WalkModel(N,S,E,W); m.curve()
                Closed subscheme of Projective Space of dimension 2 over Fraction Field of Univariate Polynomial Ring in t over Rational Field defined by:
                  (-t)*x^2*y + (-t)*x*y^2 + x*y*z + (-t)*x*z^2 + (-t)*y*z^2
                sage: m.curve('P')
                Closed subscheme of Product of projective spaces P^1 x P^1 over Fraction Field of Univariate Polynomial Ring in t over Rational Field defined by:
                  (-t)*x0*x1*y0^2 + (-t)*x0^2*y0*y1 + x0*x1*y0*y1 + (-t)*x1^2*y0*y1 + (-t)*x0*x1*y1^2
                sage: all(m.curve(inp) is m.curve('A') for inp in [1,'xyz','xy','a','A'])
                True
                sage: all(m.curve(inp) is m.curve('P') for inp in [3, 'x0x1y0y1', 'x0y0', 'p', 'projective', 'P'])
                True
                sage: all(m.curve(inp) is m.curve('W') for inp in [2, 'uvw', 'uv', 'w', 'weierstrass', 'W'])
                True

            The Weierstrass model can not be computed for some models since they are not elliptic::

                sage: m = NonEllipticC[0]; m.curve('W')
                Traceback (most recent call last):
                ...
                NonEllipticError: The kernel is not a elliptic curve --> No Weierstrass model
        '''
        model = self.model(model)

        # Computing the curve in case it is necessary
        if(not (model in self.__curve)):
            self.__curve[model] = self.ambient(model).subscheme(self.kernel(model))

        # Returning the curve
        return self.__curve[model]

    @cached_method
    def neutral_point(self, model='A'):
        r'''
            Method that return the neutral point of the elliptic curve.

            The kernel function associated to some model of walks on the quarter plane
            usually defines an elliptic curve (see method :func:`curve`). It is well known
            that points on elliptic curves define an abelian group.

            This method returns the neutral element of that group (if the curve is elliptic) or
            raise a ``TypeError`` in case the model does not define an elliptic curve.

            * In the Weierstrass model, the neutral point is always the point at the infinity
              line, i.e., `(0:1:0)`.
            * In other models, we compute the transformation from the Weierstrass model and the
              corresponding model and use the method :func:`daeg1.alggeo.apply_map` on
              `(0:1:0)` for getting the point.

            INPUT:
                * ``model``: it decides the point that is returned (see method :func:`model`)

            EXAMPLES::

                sage: from daeg1.walkmodel import *
                sage: m = WalkModel(N,E,S,W); m.neutral_point()
                (0 : 0 : 1)
                sage: m.neutral_point('W')
                (0 : 1 : 0)
                sage: m.neutral_point('P')
                (0 : 1 , 0 : 1)

            We can check that all the models have the same neutral point in the Weierstrass model::

                sage: all(m.curve('W')([0,1,0]) == m.neutral_point('W') for m in FiniteGroup + EllipticC) # long time
                True

            Not always the neutral point is the origin in the XY models::

                sage: m = dic_models["FG-BMM-2.5"]; m.neutral_point()
                (0 : -1 : 1)
                sage: m = dic_models["wIB.1"]; m.neutral_point()
                (-1 : 0 : 1)

            Sometimes, this neutral point can also be an algebraic element over t::

                sage: m = dic_models["FG-BMM-1.02"]; m.neutral_point('P')
                verbose 0 ...
                (0 : 1 , -1/2*r : 1)
        '''
        model = self.model(model)
        curve = self.curve(model)

        if(not model in self.__neutral):
            if(model == "W"): # easy Weierstrass model
                self.__neutral[model] = curve([0,1,0])
            else: # for other models we compute its image
                self.__neutral[model] = apply_map(self.map('W', model), self.neutral_point("W"))
        return self.__neutral[model]

    ## TODO: remove --> move to alggeo
    @dLogFunction
    def intersection(self, poly, model="A"):
        from sage.categories.pushout import pushout
        model = self.model(model)
        poly = self.ring(model)(poly)

        if(model == "A" or model == "W"): # Case with three variables
            x,y,z = self.vars(model)

            k = self.kernel(model)
            curve = self.curve(model)

            factors = poly.factor(proof=False)
            result = []
            for factor in factors:
                f = factor[0]
                ## Simple case: one monomial
                if((len(f.variables()) == 1) and (f.variables()[0].divides(f))):
                    vars = [x,y,z]
                    v = f.variables()[0]; i = vars.index(v); vars.pop(v)

                    aux_k = k(**{str(v) : 0}) # Bivariate homogenous polynomial
                    points = zeros_bihom(aux_k, vars, algebraic=lambda r, p, n : self.alg_extension(p))

                    # Casting the point to points on the curve
                    result += [curve(list(P).insert(i, 0)) for P in points]
                else:
                    dlogging.warning("WalkModel.intersection: found a difficult factor in %s --> %s (Ignoring these points)" %(poly, f))
            return list(set(result))
        elif(model == "P"): # Case with four variables
            x0,x1,y0,y1 = self.vars(model)

            k = self.kernel(model)
            curve = self.curve(model)

            factors = poly.factor(proof=False)
            result = []
            for factor in factors:
                f = factor[0]
                ## Case all variables are x0,x1
                if(all(v in [x0,x1] for v in f.variables())):
                    points = zeros_bihom(f, [x0,x1], algebraic=lambda r, p, n : self.alg_extension(p))
                    for P in points:
                        R = pushout(k.base_ring(), pushout(parent(P[0]),parent(P[1])))
                        aux_k = k.change_ring(R)(x0=P[0],x1=P[1])
                        QPoints = zeros_bihom(aux_k,[y0,y1], algebraic=lambda r, p, n : self.alg_extension(p))
                        result += [point_extension([P[0],P[1],Q[0],Q[1]], curve) for Q in QPoints]
                ## Case all variables are y0,y1
                elif(all(v in [y0,y1] for v in f.variables())):
                    points = zeros_bihom(f,[y0,y1], algebraic=lambda r, p, n : self.alg_extension(p))
                    for Q in points:
                        R = pushout(k.base_ring(), pushout(parent(Q[0]),parent(Q[1])))
                        aux_k = k.change_ring(R)(y0=Q[0],y1=Q[1])
                        PPoints = zeros_bihom(aux_k,[x0,x1], algebraic=lambda r, p, n : self.alg_extension(p))
                        result += [point_extension([P[0],P[1],Q[0],Q[1]], curve) for P in PPoints]
                else:
                    dlogging.warning("WalkModel.intersection: found a difficult factor in %s --> %s (Ignoring these points)" %(poly, f))
            return list(set(result))

    @cached_method
    def add_P(self, point, model="W"):
        r'''
            Method to get the rational maps that add a point (in an elliptic curve).

            This method computes the rational representation for adding a point on an elliptic curve. Since
            points on elliptic curves make an abelian group, we can, fixed `P` in the curve, we can take the
            map `s_P` defined with `s_P(Q) = P+Q`.

            It is known that these maps `s_P` are birrational maps. In fact, they are isomorphisms. This method just
            compute that rational map.

            In the case of an elliptic curve in Weierstrass form, this map is geometrically seasy to compute and
            that is the method we use here. If the map required is not on the Weierstrass form, we translate into
            such model and then compute the map there.

            This method is cached.

            TODO:
                * Add INPUT, OUTPUT sections
                * Add examples
        '''
        model = self.model(model)
        curve = self.curve(model)
        point = curve(point)

        # Case of a non-Weierstrass model
        if(model != "W"):
            f = self.map("W", model)
            g = self.map(model, "W")
            wP = apply_map(g,point)
            h = self.add_P(wP)
            morphism = f*h*g

            return simpl_morphism(morphism)
        # Case on the Weierstrass model
        u,v,w = self.vars("W")
        H = Hom(curve,curve)
        # Trivial case: point at infinity
        if(point == curve([0,1,0])):
            return H.identity()

        # Affine case: we may assume w=1
        a = point[0]/point[2]; b = point[1]/point[2]
        du = a*w - u; dv = b*w - v
        C = -self.kernel(model)(w=1).coefficient(u**3)/self.kernel(model)(w=1).coefficient(v**2)
        ## The line going from (a,b) to (u,v) can be described with l*(a,b) + (1-l)*(u,v) = (u,v) + l*(du,dv)
        ## Then we plug in the kernel equation C*(u+l*du)^3 - (v+l*dv)^2 + A*(u+l*du) + B = 0
        ## This leads to an equation of the shape M*l^3 + N*l^2 + K*l = 0. Then l = -(M+N)/M.
        ## M --> C*du^3
        ## N --> 3*C*u*du^2 - dv^2
        ## K --> 3*C*u^2*du - 2*v*dv + A*du
        ## Then we can plug that value of l to compute the third point on the line
        ## U = (C*u*du^3 - C*du^4 - 3*C*u*du^3 + du*dv^2)/C*du^3
        ## V = (C*v*du^3 - C*du^3*dv - 3*C*u*du^2*dv + dv^3)/C*du^3
        ## Now we see that the highest degree is 4, so the homogination will raise all terms to degree 4
        ## du --> a*w - u; dv --> b*w - v
        U = (C*u*du**3 - C*du**4 - 3*C*u*du**3 + w*du*dv**2)
        V = -(C*v*du**3 - C*du**3*dv - 3*C*u*du**2*dv + w*dv**3)
        W = C*w*du**3

        morphism = H([U,V,W])
        return simpl_morphism(morphism)

    @cached_method
    def inv_P(self, point, model="W"):
        r'''
            Method to compute the elliptic inverse of a point.

            Points over elliptic curves make an abelian group. This method receives a point
            on the elliptic curve for the model and compute its additional inverse, i.e.,
            given `P` in the curve, we compute `Q` such that `P+Q = O`.

            In the particular case of the Weierstrass model, this inverse is easy to compute:
                * If `P = (0:1:0)`, then `P = O` and we return `O`.
                * If `P = (a:b:1)`, then `Q = (a:-b:1)`.

            This method is cached.

            TODO:
                * Add INPUT, OUTPUT sections
                * Add examples
        '''
        model = self.model(model)
        curve = self.curve(model)
        point = curve(point)

        # Case of a non-Weierstrass model
        if(model != "W"):
            f = self.map("W", model)
            g = self.map(model, "W")
            return apply_map(f, self.inv_P(apply_map(g,point)))

        # Case on the Weierstrass model
        if(point == curve([0,1,0])): # Neutral element
            return point
        # Affine case: we reflect v
        return curve([point[0], -point[1], point[2]])

    def map(self, dom, codom):
        r'''
            Method to get the birrational map between the models for the kernel curve.

            This method return a map etween different representations of the kernel curve.
            Since all these representacions are for the same curve, these maps are birational.
        '''
        dom = self.model(dom); codom = self.model(codom)

        # Computing the map in case it is necessary
        if(not ((dom,codom) in self.__maps)):
            if(dom == codom):
                E = self.curve(dom)
                self.__maps[(dom,dom)] = Hom(E,E).identity()
            if(dom == "W" or codom == "W"): # Weierstrass model
                self.kernel('W')
                if(dom == "P" or codom == "P"): # W and P
                    self.__maps[(dom,codom)] = self.map("A",codom) * self.map(dom, "A")
                else: # W and A --> computed while computing the kernel of W
                    self.kernel("W")
            else: ## Either (A,P) or (P,A)
                Ea = self.curve("A")
                x,y,z = self.vars("A"); x0,x1,y0,y1 = self.vars("P")
                Ep = self.curve("P")
                self.__maps[("A", "P")] = Hom(Ea, Ep)([x,z,y,z])
                self.__maps[("P", "A")] = Hom(Ep, Ea)([x0*y1, y0*x1, x1*y1])

        # Returning the map
        return self.__maps[(dom,codom)]

    def A(self, i, model="A"):
        r'''
            Model to get the coefficients in `y` of the kernel equation.

            For any walk model, we can write the affine kernel equation as

            .. MATH::

                K(x,y,t) = A_{-1}(x,t) + A_0(x,t)y + A_1(x,t)y^2

            This method return (in the corresponding model) the corresponding
            coefficient indicated by the input ``i``. This value can be directly
            extracted from the kernel equation in the affine (``A``) and projective
            (``P``) models. For the Weierstrass model, we compute it on the affine
            model and compute its corresponding pullback.

            For the affine case, the output involve the projective variable `z` and
            for the projective case, the output is homogeneous in `x_0` and `x_1`.

            INPUT:
                * ``i``: the index of the coefficient we want to extract.
                * ``model``: the model in which we want the coefficient.
        '''
        model = self.model(model)

        if(not ((model,i) in self.__A)):
            if(model == "A"): # The affine case
                k = self.kernel(model)
                _,y,_ = self.vars(model)
                if(i >= -1 and i <= 1):
                    self.__A[(model, i)] = k.coefficient({y:1+i})
            if(model == "P"): # The projective case
                k = self.kernel(model)
                _,_,y0,y1 = self.vars(model)
                if(i >= -1 and i <= 1):
                    self.__A[(model, i)] = k.coefficient({y0:1+i,y1:2-(1+i)})
            if(model == "W"): # The Weierstrass case
                self.__A[(model,i)] = simplify_rational_variety(pullback(self.map('W','A'))(self.A(i,"A")), self.map('a','w').codomain())
        return self.__A[(model,i)]

    def B(self, i, model="A"):
        r'''
            Model to get the coefficients in `x` of the kernel equation.

            For any walk model, we can write the affine kernel equation as

            .. MATH::

                K(x,y,t) = B_{-1}(y,t) + B_0(y,t)x + A_1(y,t)x^2

            This method return (in the corresponding model) the corresponding
            coefficient indicated by the input ``i``. This value can be directly
            extracted from the kernel equation in the affine (``A``) and projective
            (``P``) models. For the Weierstrass model, we compute it on the affine
            model and compute its corresponding pullback.

            For the affine case, the output involve the projective variable `z` and
            for the projective case, the output is homogeneous in `y_0` and `y_1`.

            INPUT:
                * ``i``: the index of the coefficient we want to extract.
                * ``model``: the model in which we want the coefficient.
        '''
        model = self.model(model)

        if(not ((model,i) in self.__B)):
            if(model == "A"): # The affine case
                k = self.kernel(model)
                x,_,_ = self.vars(model)
                if(i >= -1 and i <= 1):
                    self.__B[(model, i)] = k.coefficient({x:1+i})
            if(model == "P"): # The projective case
                k = self.kernel(model)
                x0,x1,_,_ = self.vars(model)
                if(i >= -1 and i <= 1):
                    self.__B[(model, i)] = k.coefficient({x0:1+i,x1:2-(1+i)})
            if(model == "W"): # The Weierstrass case
                self.__A[(model,i)] = simplify_rational_variety(pullback(self.map("W","A"))(self.B(i,"A")), self.map('a','w').codomain())
        return self.__B[(model,i)]

    ##########################################################################################
    ## Discriminant and Eisenstein invariants
    def discriminant(self, var, model="A"):
        r'''
            Method to compute the discriminant of the kernel with respect to one of its variables.

            For any walk model, we can write the affine kernel equation as

            .. MATH::

                K(x,y,t) = A_{-1}(x,t) + A_0(x,t)y + A_1(x,t)y^2

            .. MATH::

                K(x,y,t) = B_{-1}(y,t) + B_0(y,t)x + A_1(y,t)x^2

            So we can look to the kernel equation as a degree 2 polynomial in `x` or a degree 2 
            polynomial in `y`. This method computes the discriminant of the kernel either in `x`
            or `y` leading to a polynomial in the other variable which roots are the points where 
            the involution methods `\iota_1` and `\iota_2` (see method :func:`i`) have fixed points.

            It is pretty obvious that the kernel curve is smooth (i.e., elliptic -- :func:`is_elliptic`) 
            if there is no point that is fixed by both `\iota_1` and `\iota_2`, i.e., for any 
            zeros `P_x \in \mathbb{P}` of the discriminant w.r.t. `y` and `Q_y \in \mathbb{P}`
            of the discriminant w.r.t. `x`, we have

            .. MATH::

                K(P_x, Q_y, t) \neq 0

            Which means that the point `(P_x,Q_y)` is not in the kernel curve.
            
            TODO:
                * Add INPUT OUTPUT sections
                * Add tests and examples
        '''
        model = self.model(model)
        if(var == "x" or var == 1):
            var = 1
        elif(var == "y" or var == 2):
            var = 2

        if(not ((model,var) in self.__discriminant)):
            if(model == "P"):
                k = self.kernel(model)
                x0,_,y0,_ = self.vars(model)
                if(var == 1): # discr deleting y
                    self.__discriminant[(model,var)] = k(y1=1).discriminant(y0)
                elif(var == 2): # discr deleting x
                    self.__discriminant[(model,var)] = k(x1=1).discriminant(x0)
            elif(model == "A"):
                x,y,z = self.vars(model)
                d = self.discriminant(var,"P")
                if(var == 1):
                    self.__discriminant[(model,var)] = self.ring(model)(d(x1=1,x0=x,y0=y,y1=1)).homogenize(z)
                elif(var == 2):
                    self.__discriminant[(model,var)] = self.ring(model)(d(y1=1,y0=y,x0=x,x1=1)).homogenize(z)
            elif(model == "W"):
                self.__discriminant[(model,var)] = pullback(self.map("W","A"))(self.discriminant(var,"A"))
        return self.__discriminant[(model,var)]

    @cached_method
    def eisenstein(self,invariant="F"):
        r'''
            Method to compute the Eisenstein's invariants of the curve.

            There are three different invariants for the kernel curve called Eisenstein's invariants.
            These invariants only depends on the kernel function (see method :func:`kernel`) and characterize
            esily whether the curve is elliptic or not (see method :func:`is_elliptic`).

            INPUT:
                * ``invariant``: the user has to provide its name (i.e., ``D``, ``E`` or ``F``) or a number
                  (resp. ``1``, ``2`` or ``3``).

            OUPUT:
            
            The corresponding invariant in the corresponding field.
            
            TODO:
                * Add INPUT OUTPUT sections
        '''
        if(invariant == "F" or invariant == 3):
            E = self.eisenstein("E")
            D = self.eisenstein("D")
            return -(D**3 - 27*E**2)

        ## The invariant is "E" or "D"
        x0,x1,_,_ = self.vars("P")
        p = self.discriminant(1,"P")

        a0,a1,a2,a3,a4 = (self._F(p.coefficient({x0:i,x1:4-i})/binomial(4,i)) for i in range(5))
        if(invariant == "D" or invariant == 1):
            return a0*a4 + 3*a2**2 - 4*a1*a3
        elif(invariant == "E" or invariant == 2):
            return a0*a3**2 + a1**2*a4 - a0*a2*a4 - 2*a1*a2*a3 + a2**3
        else:
            raise ValueError("Incorrect invariant asked for eisenstein. Only 'D' (1), 'E' (2) or 'F' (3) are allowed")

    @cached_method
    def modulus(self):
        r'''
            Method to check get the modulus of the elliptic curve.

            This method compute the corresponding invariant of the curve when the curve
            is elliptic (see method :func:`is_elliptic`).
            
            TODO:
                * Add INPUT OUTPUT sections
                * Add tests and examples
        '''
        D = self.eisenstein("D")
        F = self.eisenstein("F")

        if(F == 0):
            raise NonEllipticError("The curve is not elliptic")
        else:
            return (D**3)/(-F)

    @cached_method
    def g2(self):
        r'''
            Method to check get the `g_2` invariant of the curve.

            This method compute the corresponding invariant of the curve. If the curve
            is elliptic (see method :func:`is_elliptic`) then this invariant is the
            constant coefficient in the Weierstrass form of the curve.
            
            TODO:
                * Add INPUT OUTPUT sections
                * Add tests and examples
        '''
        if(not self.is_elliptic()):
            raise NonEllipticError("The model has not a elliptic kernel")
        return self.eisenstein("D")

    @cached_method
    def g3(self):
        r'''
            Method to check get the `g_3` invariant of the curve.

            This method compute the corresponding invariant of the curve. If the curve
            is elliptic (see method :func:`is_elliptic`) then this invariant is the
            constant coefficient in the Weierstrass form of the curve.
            
            TODO:
                * Add INPUT OUTPUT sections
                * Add tests and examples
        '''
        if(not self.is_elliptic()):
            raise NonEllipticError("The model has not a elliptic kernel")
        return -self.eisenstein("E")

    @cached_method
    def is_elliptic(self):
        r'''
            Method to check wether the kernel curve is elliptic or not.

            This method compute the corresponding invariant of the curve and, due to 
            its form, being elliptic is equivalent to have a non-zero invariant.
            
            TODO:
                * Add INPUT OUTPUT sections
                * Add tests and examples
        '''
        return self.eisenstein("F") != 0

    ##########################################################################################
    ## Methods for Theorem 1 on Kourkova-Raschel 2015
    def KR_f(self, var, model="A"):
        r'''
            Method for computing the functions `f_x` and `f_y` from K.R.-2015

            The kernel equation for the model looks like

            .. MATH::

                \begin{array}{rcl}
                    0& = & Q(x,y,t)K(x,y,t) - \\
                     &   & Q(x,0,t)K(x,0,t) - \\
                     &   & Q(0,y,t)K(0,y,t) + \\
                     &   & Q(0,0,t)K(0,0,t) + \\
                     &   & xy 
                \end{array}

            There are three pieces that are evaluations of the first term. We are focused now on the
            two middle terms, which are just the evaluations in `y=0` and `x=0` of the product
            of the generating function and the kernel (denoted by `r_x` and `r_y` respectively)

            On the other hand, we have defined `\tau` a map that perform to ivolutions within the curve
            and that defines a point `Q` such that `\tau(P) = P \oplus Q` for all `P` in the curve. We can
            then study the behavior of the two sections with respect to this point:

            .. MATH::

                \begin{array}{rcl}
                    f_x & = & r_x \tau - r_x = y(x\iota_y - x)\\
                    f_y & = & r_y \tau - r_y = x(y\iota_x - y)
                \end{array}

            This method computes these functions and transform then into the required model.

            REMARK: 
                * this method, for variable `2`, is equivalent to the method :func:`b` that we defined using the paper
                  by Dreyfus, Hardoin, Roques and Singer.
                * this method, for variable `1`, is related to the method :func:`b`, but now with a prefactor of
                  :func:`i` for the variable `x` 

            INPUT:
                * ``var``: the name or number of the varible. Any element which string is ``'x'`` or ``'y'``, or
                  the numbers 1 (for `x`) and 2 (for `y`).
                * ``model``: model of the curve we want the result. See method :func:`model` for further information.

            OUTPUT::

                sage: from daeg1 import *
                sage: all(m.b(2)(x=x0/x1,y=y0/y1,z=1) == m.KR_f(2,'p') for m in AllModels if (not m.is_singular())) # long time
                True
                sage: all(m.b(1)(x=x0/x1,y=y0/y1) == pullback(m.iota(1,'p'))(m.KR_f(1, 'p')) for m in AllModels if (not m.is_singular())) # long time
                True
        '''
        model = self.model(model)
        if(str(var) == "x" or var == 1):
            var = 1
        elif(str(var) == "y" or var == 2):
            var = 2
        
        if(not (var, model) in self.__KR_f):
            if(model == 'P'):
                x = x0/x1; y = y0/y1
                
                if(var == 1): self.__KR_f[(var, model)] = y*(pullback(self.iota(2, 'P'))(x)-x)
                elif(var == 2): self.__KR_f[(var, model)] = x*(pullback(self.iota(1, 'P'))(y)-y)
            else:
                to_model = pullback(self.map(model, 'P'))
                self.__KR_f[(var, model)] = to_model(self.KR_f(var, 'P'))

        return self.__KR_f[(var, model)]

    def KR_poles_f(self, var, model="P"):
        r'''
            Method to get the poles of the functions `f_x` and `f_y`.

            This method computes the poles of the functions `f_x` and `f_y` defined in the 
            method :func:`KR_f` using the expression from which we computed the functions.

            This computations implies computing the intersection of the elliptic curve with
            the lines at infinity for `x` and `y`, which may lead to some long computations
            and some algebraic extensions.
        '''
        model = self.model(model)
        if(str(var) == "x" or var == 1):
            var = 1
        elif(str(var) == "y" or var == 2):
            var = 2

        if(not (var, model) in self.__KR_poles_f):
            if(model == "W"):
                to_W = self.map('P', 'W')
                self.__KR_poles_f[(var, model)] = [apply_map(to_W, pole) for pole in self.KR_poles_f(var, 'P')]
            else:
                _,x1,_,y1 = self.vars('P')
                f = self.KR_f(var, 'P') 
                curve = self.curve('P')
                x_inf_poles = self.intersection(x1, 'P'); y_inf_poles = self.intersection(y1, 'P')

                if(var == 1):
                    candidates = y_inf_poles + x_inf_poles + [apply_map(self.iota(1,'P'),pole) for pole in y_inf_poles]
                elif(var == 2):
                    candidates = x_inf_poles + y_inf_poles + [apply_map(self.iota(2,'P'),pole) for pole in x_inf_poles]

                self.__KR_poles_f[(var, model)] = list(set([pole for pole in candidates if asymptotics(curve, f, pole)[0] < 0]))

        return self.__KR_poles_f[(var, model)]
        
    
    ##########################################################################################
    ## Analytic analysis of functions on the curve
    ## TODO: remove --> move to alggeo
    def poles(self, func, model="A"):
        r'''
            Method for computing poles of a rational function on the curve.

            This method takes a rational function over the elliptic curve defined in the model and
            computes its poles. This method transform the problem to the double projective model
            (see method :func:`model` for further information).

            In this model, we compute the zeros of the denominator of the rational function and, since
            these denominators are bihomogeneous polynomials, we can use methods like
            :func:`~daeg1.alggeo.zeros_bihom` to compute the roots of it and then compute the points
            of the curve that annihilates that denominator.

            Then we can use the method :func:`~daeg1.alggeo.asymptotics` to check whether these candidates
            are indeed poles or not.

            WARNING:
                * The result is given either on the double projective model (model ``P``) or the Weierstrass
                  model (model ``W``).
                * The method catched the result internally.

            INPUT:
                * ``func``: rational function we want to compute poles. It has to be in the model given
                  by the argument ``model``.
                * ``model``: the model we are working on. See method :func:`model` for further information.

            OUTPUT:

            A list with the poles of ``func`` on the curve. These points are given by projective coordinates
            either in the `(x_0:x1,y_0:y_1)` model (for models ``A`` and ``P``) or in the `(u:v:w)` model (for
            model ``W``).

            TODO:
                * Add examples and tests to this doc.
        '''
        model = self.model(model)

        if(not ((func,model) in self.__poles)):
            # Weiertrass case
            if(model == "W"):
                poles = self.poles(pullback(self.map("P","W"))(func))
                poles = [apply_map(self.map("P", "W"), pole) for pole in poles]
            # Affine case
            elif(model == "A"):
                x0,x1,y0,y1 = self.vars("P")
                func = func(z=1)(x=x0/x1, y=y0/y1)
                poles = self.poles(func, "P")
            ## Projective case
            elif(model == "P"):
                d = func.denominator()
                # Compute the points on the curve that vanishes d
                # The result will be points on self.curve("P")
                # I.e., P[0] = (x0:x1), P[1] = (y0:y1).
                poles = self.intersection(d, "P")
                poles = [el for el in poles if asymptotics(self.curve('P'), func, el)[0] < 0]

            # Adding the new value
            self.__poles[(func, model)] = poles

        return self.__poles[(func, model)]

    @cached_method
    def only_pole_point(self, order, point, model="P"):
        r'''
            Method to compute a function with a single pole of a particular order.

            Given an elliptic curve `E` and a point `P \in E`, there are (using Riemman-Roch theorem)
            rational functions over `E` that have poles only at `P` with order `n` and are regular
            elsewhere for all `n \geq 2`.

            This method compute such function given the order of the pole and the point on the curve.

            If `E` is in Weierstrass form: 
            
            .. MATH::
            
                E = \{(u:v:w)\ :\ 4u^3 - v^2w + Auw^2 + Bw^3 = 0\}

            then at infinity (`P = (0:1:0)`), we know that `u/w` has a pole of order 2 and `v/w` has a pole
            of order 3. Hence for any `n \geq 2` we can write as `n = 3 + 2m` so the function `vu^m` has a unique
            pole of order `n` at `(0:1:0)`.

            If `E` is in Weierstrass form and `P \neq (0:1:0)`, there is a rational function `\varphi` such that
            `\varphi(Q) = Q \ominus P`. If we consider now `\varphi^*(g)` for any rational function `g \in \mathbb{C}(E)`,
            then `\varphi^*(g)(P) = g(\varphi(P)) = g(0:1:0)`. This means that the behavior of `\varphi^*(g)` at `P`
            is the behavior of `g` at `(0:1:0)`. This means that:

            * `\varphi^*(u/w)` has a unique pole of order 2 at `P`.
            * `\varphi^*(v/w)` has a unique pole of order 3 at `P`.

            Finally, if `E` is **not** in Weierstrass form, but we have a map `\psi: E \rightarrow \tilde{E}` to its Weierstrass form, then
            for any `g \in \mathbb{C}(\tilde{E})` and `P \in E`, `\psi^*(g)(P) = g(\psi(P))`. Hence, the behavior of
            `\psi^*(g)` at `P` is the same behavior as `g` has in `\psi(P)`.

            INPUT:
                * ``order``: the order of the pole. It mast be a possitive integer greater than 1.
                * ``point``: the point where we want to do the computations
                * ``model``: the model to compute the function. See method :func:`model` for further information.

            OUTPUT:
                * A rational function that has a unique pole at ``point`` of the given order.
                * If the model is not elliptic (see method :func:`is_elliptic`) the method raises a :class:`NonEllipticError`.

            TODO:
                * Add tests and examples
        '''
        model = self.model(model)
        if(not self.is_elliptic()):
            raise NonEllipticError("The model is not elliptic --> no higher polar part defined")
        order = Integer(order)
        if(order <= 1):
            raise ValueError("The order has to be greater or equal to 2")

        point = point_extension(point, self.curve(model))

        if(model != "W"): # Non-Weierstrass case
            psi = self.map(model, "W"); ppsi = pullback(psi)
            f = self.only_pole_point(order, apply_map(psi, point), "W")
            return ppsi(f)
        elif(point != self.curve("W")([0,1,0])):
            phi = self.add_P(self.inv_P(point)); pphi = pullback(phi)
            f = self.only_pole_point(order, (0,1,0), "W")
            return pphi(f)
        else:
            u,v,w = self.vars("W")
            if(order % 2 == 1):
                m = (order-3)//2
                return (v/w)*(u/w)**m
            else:
                m = order//2
                return (u/w)**m

    def higher_polar_part(self, func, point, model="P"):
        r'''
            Method to compute the *higher polar part* of a rational function at a point.

            Given an elliptic curve `E` and a point `P \in E`, there are (using Riemman-Roch theorem)
            rational functions over `E` that have poles only at `P` with order `n` and are regular
            elsewhere for all `n \geq 2`. Hence, we can distinguish all the polar part of any function
            up to the order 2.

            The higher polar part of `f \in \mathbb{C}(E)` at a point `P` is a rational function `g`
            such that `g` only has poles at `P` and `\operatorname{ord}_P(f-g) \geq -1`. See method :func:`only_pole_point`
            to see how to compute the basic pieces of `g`. With those basic pieces, we can use linear algebra
            to compute `g` completely.

            WARNING: The method catched the result internally.

            INPUT:
                * ``func``: rational function we want to analyze.
                * ``point``: point on the curve to compute the higher polar part.
                * ``model``: the model we are working with. See method :func:`model` for further information.

            OUTPUT:
                This method returns a rational function. The method :func:`daeg1.alggeo.simplify_rational_variety` will be applied
                before returning, so some kind of cannonical output is expected.

            TODO:
                Add examples and tests.
        '''
        if(not self.is_elliptic()):
            raise NonEllipticError("The model is not elliptic --> no higher polar part defined")
        model = self.model(model)
        ## Basic variables (these lines check the input is in proper format)
        F = FractionField(self.ring(model))
        func = F(func)
        point = point_extension(point, self.curve(model))

        polar_func = polar_part(self.curve(model), func, point,True)[0]; higher_func = vector(polar_func[2:])
        if(len(higher_func) == 0):
            return F.zero()
        pole_funcs = [self.only_pole_point(i+2, point, model) for i in range(len(higher_func))]
        pole_coefficients = Matrix([polar_part(self.curve(model), pole_funcs[i], point,True)[0][2:] + (len(pole_funcs)-i-1)*[0] for i in range(len(pole_funcs))])

        return simplify_rational_variety(sum(map(lambda p,q: p*q, list(pole_coefficients.solve_left(higher_func)), pole_funcs)), self.curve(model))

    def residue(self, func, model = "P"):
        r'''
            Method to get the residue of a function.

            The higher polar part of a rational function `f` over an elliptic curve `E`
            on a point `P` is defined as a rational function `g \in \mathbb{C}(E)` that
            has a unique pole at `P`and suc that `ord_P(f - g) \geq -1`. See method
            :func:`higher_polar_part` for further information.

            Since these polar parts have a pole localized in just one point, we can gather all them together
            and *remove* the polar behavior of `f` everywhere. This remaining function is called *residue*:

            .. MATH::

                f = res(f) + \sum_P pol_P(f)

            **REMARK**: if `res(f)` has no poles, then it is constant on the curve.

            INPUT:
                * ``func``: rational representation of the function `f`.
                * ``model``: model to interpret the function `f`. See method :func:`model` for further
                  information.

            OUTPUT:
                A tuple with the values `(res(f), \sum_P pol_P(f))`.

            TODO:
                * Add examples and tests

        '''
        model = self.model(model)

        poles = self.poles(func, model)
        hpp = [self.higher_polar_part(func, pole, model) for pole in poles]
        shpp = simplify_rational_variety(sum(hpp), self.curve(model))

        return (simplify_rational_variety(func - shpp, self.curve(model)), shpp)

    def is_multiple_pole(self, func, point, model = "P"):
        r'''
            Boolean for having a pole at a point of order higher than 1.

            This method computes for a given point and function if it has a multiple pole
            at a particular point. See method :func:`daeg1.alggeo.asymptotics` for further
            information.

            INPUT:
                * ``func``: rational function we want to check
                * ``point``: point on the curve we want to check.
                * ``model``: model we are working on. See method :func:`model` for further
                  information.

            OUTPUT:
                ``True`` if the function described by ``func`` has a multiple pole at ``point``.
                False otherwise.

            TODO:
                * Add examples and tests
        '''
        model = self.model(model)
        curve = self.curve(model)
        point = point_extension(point, curve)

        return asymptotics(curve, func, point)[0] < -1

    def orbits(self, points, bound=10, model="P"):
        r'''
            Method that looks `\tau`-orbits in a list of points up to some bound.

            This method receives a list of points on the curve defined by the kernel function and
            tries to get which of them are related with the map `\tau`. Since this can not always
            be done, we fixed a maximal bound to look for that relation.

            INPUT:
                * ``points``: list of point on the curve.
                * ``bound``: maximal distance between the points.

            OUTPUT:
                A tuple ``(orbits, jumps)`` whew ``orbits`` is a list with all the orbits we have found and
                ``jumps`` a list of integers such that ``\tau^jumps[i][j](orbits[i][j]) == orbits[i][j+1]``.

            TODO:
                * Add examples and tests
        '''
        model = self.model(model)
        curve = self.curve(model)

        points = [point_extension(P, curve) for P in points]
        tau = self.tau(model)

        dic = {}
        for i in range(len(points)):
            P = points[i]; nP = P
            for j in range(1,bound+1):
                nP = apply_map(tau, nP)
                if(points.count(nP) > 0):
                    if(nP != P):
                        dic[(i,points.index(nP))] = j
                    break

        # dic[(i,j)] = n --> points[j] = tau^n(points[i])
        try:
            poset = Poset((range(len(points)),dic.keys()))
        except ValueError: # cycle detected
            g = DiGraph([range(len(points)), dic.keys()], format="vertices_and_edges")
            for cycle in g.all_cycles_iterator(simple=True):
                g.delete_edge((cycle[-2],cycle[-1]))
            poset = Poset(g)
        orbits = [[points[i] for i in chain] for chain in poset.maximal_chains()]
        jumps = [[dic[(chain[i],chain[i+1])] for i in range(len(chain)-1)] for chain in poset.maximal_chains()]

        for i in range(len(orbits)):
            orbits[i].reverse()
            jumps[i].reverse()
        # orbits[i][0] = tau^(-sum(jumps[i][:j]))(orbits[i][j])

        return (orbits,jumps)

    def orbital_polar_part(self, func, poles, point, bound=5, w_orbits=False, model="P"):
        r'''
            Method to compute the orbital polar part at one point.

            This method computes the orbital polar part of a function at one point. In
            :func:`higher_polar_part` we describe what is on elliptic curves the higher polar
            part of a rational function `f`. Now, given `\tau`, these poles are grouped
            in orbits. The orbital polar part is defined as follows:

            .. MATH::

                opol_P(f) = \sum_{k \in \mathbb{Z}} pol_P(\tau^{*n}(f)).

            Intuitively, we move with `\tau` all the poles of the orbit of `P` to `P` and then
            we add all the polar behavior of the function.

            Interestingly enough, if `\tau(P) = Q`, then `\tau(opol_P(f)) = opol_Q(f)`.

            INPUT:
                * ``func``: rational funtion we are analyzing.
                * ``poles``: poles of ``func`` or `\tau`-orbits of the poles. See ``w_orbits``.
                * ``point``: point on the curve we are studying.
                * ``bound``: in case it is needed, the bound for looking for `\tau`-orbits in the poles.
                * ``w_orbits``: boolean argument deciding the type of the input of the poles. If set to
                  ``True``, the argument ``poles`` will be read as the output of the method :func:`orbits`,
                  otherwise we use it as a list of poles of ``func`` and use the argument ``bound`` for building
                  the corresponding `\tau`-orbits.
                * ``model``: model of the elliptic curve we are working on. See method :func:`model` for
                  further information.

            TODO:
                * Add tests and examples
        '''
        model = self.model(model); curve = self.curve(model)
        tau = self.tau(model); itau = self.itau(model)
        ptau = pullback(tau); pitau = pullback(itau)
        point = point_extension(point, curve)

        if(not w_orbits):
            poles = [point_extension(pole, curve) for pole in poles]
            orbits, jumps = self.orbits(poles, bound, model)
        else:
            orbits,jumps = poles
            orbits = [[point_extension(pole, curve) for pole in orbit] for orbit in orbits]

        for orbit in orbits:
            if(point in orbit):
                break
        jump = jumps[orbits.index(orbit)]
        pos = orbit.index(point)

        ## At this point, we have that point == orbit[pos]
        hpp = [self.higher_polar_part(func, pole, model) for pole in orbit]
        cum_jump = [sum(jump[i] for i in range(j,pos)) + sum(-jump[i] for i in range(pos,j)) for j in range(len(orbit))]

        to_apply = [pitau**(-el) if el < 0 else ptau**el for el in cum_jump]
        return simplify_rational_variety(sum(to_apply[i](hpp[i]) for i in range(len(hpp))), self.curve(model))

    @dLogFunction
    def reduction(self, func, poles=None, jumps=None, model="P"):
        r'''
            Method that computes the decomposition of a rational function w.r.t. `\tau`.

            In the methods :func:`higher_polar_part`, :func:`residue` and :func:`orbital_polar_part`
            we have described several descriptions of the poles of rational functions over the elliptic
            curve described by :func:`kernel`. In fact, we know that, for any `f \in \mathbb{C}(E)`:

            .. MATH::

                f = res(f) + \sum_{P \in E} pol_P(f).

            In fact, that sum over `P \in E` is finite since the number of poles of `f` is finite. Now
            we also know that these poles can be grouped in `\tau`-orbits (see method :func:`orbits`). Then,
            for any pole `P` of `f`:

            .. MATH::

                \sum_{n \in \mathbb{Z}} pol_{\tau^n(P)}(f) = opol_P(f) + \tau(h) - h,

            for some particular `h \in \mathbb{C}(E)`. This infinite sum is not infinite since it only applies
            for those `n` that `\tau^n(P)` was a pole of `f`. Let `P_0,...,P_r` be a minimal set of poles
            of `f` such that all poles can be obtainin shifting these poles by `\tau`. Then:

            .. MATH::

                f = res(f) + \sum_{i=0}^r opol_{P_i}(f) + \tau(H) - H.

            In this method we compute the three pieces: `res(f)`, the orbital polar parts of the minimal
            set of poles, and `H`.

            **WARNING**: this method caches internally the result

            INPUT:
                * ``func``: the rational function to study.
                * ``poles``: fixed points to look the polar behavior. If given the computations of poles
                  of ``func`` will be skipped.
                * ``jumps``: \tau`-orbits of the poles. If given we skip the computation of the orbits of
                  the poles of ``func`` and the argument ``poles`` will be understood as the orbits.
                * ``model``: the model of the elliptic curve we start with. See method :func:`model` for further
                  information.

            OUTPUT:
                A triplet `(A,B,C)` such that `A` is the residue of ``func``, `B` is a tuple with the
                list of the minimal set of poles and the orbital polar parts and `C = H`.

            TODO:
                * Add tests and examples
        '''
        model = self.model(model)
        key = (func.numerator(), func.denominator(), model)
        if(not key in self.__reductions):
            curve = self.curve(model)

            if(not (jumps is None)):
                orbits = poles
            elif(not (poles is None)):
                orbits, jumps = self.orbits(poles, model=model)
            else:
                poles = self.poles(func)
                orbits, jumps = self.orbits(poles, model=model)

            min_set = [orbit[0] for orbit in orbits]
            opol = [self.orbital_polar_part(func, (orbits,jumps), pole, model=model, w_orbits=True) for pole in min_set]

            H = parent(func).zero()
            for i in range(len(min_set)):
                orbit = orbits[i]; jump = jumps[i]
                hpp = [0]+[self.higher_polar_part(func, opole, model) for opole in orbit[1:]]
                cum_jump = [sum(jump[j] for j in range(k)) for k in range(len(orbit))] #[0,*,*,...,*]

                pitau = pullback(self.itau(model))
                to_apply = [pitau**i for i in range(cum_jump[-1]+1)]

                h = 0
                for j in range(len(hpp)):
                    h += sum(to_apply[k](hpp[j]) for k in range(1,cum_jump[j]+1))
                H += h

            self.__reductions[key] = (self.residue(func)[0], (min_set, opol), simplify_rational_variety(H, curve))

        return self.__reductions[key]

    @dLogFunction
    def telescoping(self, func, model="P"):
        r'''
            Method to compute a telescoper (of possible) of a rational function over the kernel curve.

            This method takes a function `f \in \mathbb{C}(E)` and computes a telescoper equation of the shape

            .. MATH::

                L \cdot f = \tau(g) - g

            where `\tau` is the isomorphism described in :func:`tau`, `g` is a rational function over the elliptic
            curve described by the kernel equation (see method :func:`curve`) and `L` is a linear differential operator
            on the derivation `\delta` defined on the method :func:`derivative`.

            In case that is not possible, the method will raise an error with the reason.

            INPUT:
                * ``func``: rational function to telescope.
                * ``model``: model of the elliptic curve we work on. See method :func:`model` for further information.

            OUTPUT:
                A tuple with `(L,g)` where `L` is a list of coefficients for the linear operator and `g` is the rational
                certificate for the telescoper.

            TODO:
                * Add test and examples.
        '''
        model = self.model(model)
        key = (func.numerator(), func.denominator(), model)
        dlogging.info("WalkModel:telescoping: computing the telescoper for %s" %func)

        if(not key in self.__telescoper):
            curve = self.curve(model)

            dlogging.log(25, "WalkModel:telescoping: computing the poles of the rational function...")
            poles = self.poles(func)

            dlogging.log(25, "WalkModel:telescoping: computing the tau-orbits of the poles...")
            orbits, jumps = self.orbits(poles)

            if(any(len(orbit) == 1 for orbit in orbits)):
                raise ValueError("No telescoper: one orbit with pole has a unique point --> opol can not be zero")

            dlogging.log(25, "WalkModel:telescoping: computing the reduction for the rational function...")
            res, orbit_sum, h = self.reduction(func, orbits, jumps, model)
            for i in range(len(orbit_sum[0])):
                if(orbit_sum[1][i] != 0):
                    raise ValueError("No telescoper: opol different of zero.\n\t- Function: %s\n\t- Point: %s\n\t- opol: %s" %(func, orbit_sum[0][i], orbit_sum[1][i]))

            # opol(f) = 0 for all poles
            dlogging.log(25, "WalkModel:telescoping: the orbit polar parts are zero. Analyzing the residual part\n\t- Res(f): %s" %res)
            rows = [[expand_at_point(curve, res, pole, 0)[0].get(-1, 0) for pole in poles]]
            M = Matrix(rows)
            nullspace = M.left_kernel()
            total = 0
            g = h

            while(nullspace.rank() == 0):
                total += 1
                dlogging.log(22, "WalkModel:telescoping: telescoper not found. Computing the derivative %d..." %total)
                func = self.derivative(func, model) # computing delta(f)
                dlogging.log(22, "WalkModel:telescoping: computing the reduction...")
                cres, orbit_sum, h = self.reduction(func, orbits, jumps, model)
                for i in range(len(orbit_sum[0])):
                    if(orbit_sum[1][i] != 0):
                        raise ValueError("No telescoper: opol different of zero.\n\t- N.derivatives: %d\n\t- Point: %s\n\t- opol: %s" %(total, orbit_sum[0][i], orbit_sum[1][i]))
                g = simplify_rational_variety(g+h,curve)
                dlogging.log(25, "WalkModel:telescoping: computing the residual contribution...")
                rows += [[expand_at_point(curve, cres, pole, 0)[0].get(-1, 0) for pole in poles]]
                M = Matrix(rows)
                nullspace = M.left_kernel()

            dlogging.log(25, "WalkModel:telescoping: telescoper found\n\t- Telescoper: %s\n\t- Certificate: %s" %(str(nullspace.matrix()[0]), g))
            self.__telescoper[key] = (nullspace.matrix()[0], g)

        return self.__telescoper[key]

    ##########################################################################################
    ## Involuion methods
    def iota(self, var, model="A"):
        r'''
            Method that build the involutions associated to the kernel curve.

            Since, for any model with small steps we can write the kernel equation in the following
            forms:

            .. MATH::

                K(x,y) = A_{-1}(x) + A_0(x)y + A_1(x)y^2 = B_{-1}(y) + B_0(y)*x + B_1(y)*x^2

            Then we have that, fixed `x_0`, we can compute always two values for `y` that are on the
            curve and, in the same way, fixed `y_0` we can compute two possible values of `x` for
            getting point on the curve.

            This method, given one of the variables, returns the involution on the curve that fix such
            variable and swap between the two possible values for the other variable.

            This involutions are always of order two. It is interesting to remark that the computation
            of such involution is slightly different for the affine model and the projective model. However
            its computation over the Weierstrass model is just a pullback from the affine case.

            INPUT:
                * ``var``: the variable we are fixing. This input can be given as ``"x"`` or ``1`` for the
                  first variable and ``"y"`` or ``2`` for the second variable.
                * ``model``: model of the elliptic curve we work on. See method :func:`model` for further information.

            OUTPUT:
                * The corresponding involution in the required representation.
                * If the model is not elliptic (see method :func:`is_elliptic`) and the Wierstrass representation is required
                  a :class:`NonEllipticError` is raised.

            TODO:
                * Add examples.
        '''
        model = self.model(model)
        if(str(var) == "x" or var == 1):
            var = 1
        elif(str(var) == "y" or var == 2):
            var = 2

        if(not ((model,var) in self.__i)):
            E = self.curve(model)
            
            if(model == "A"): # Affine involution
                x,y,z = self.vars(model)
                if(var == 1):
                    f = Hom(E,E)([x*y*self.A(1,model), self.A(-1,model), z*y*self.A(1,model)])
                elif(var == 2):
                    f = Hom(E,E)([self.B(-1,model), x*y*self.B(1,model), z*x*self.B(1,model)])
            elif(model == "P"):
                x0,x1,y0,y1 = self.vars(model)
                if(var == 1):
                    f = Hom(E,E)([x0,x1,self.A(-1,model)*y1,self.A(1,model)*y0])
                elif(var == 2):
                    f = Hom(E,E)([self.B(-1,model)*x1,self.B(1,model)*x0,y0,y1])
            elif(model == "W"):
                f = self.map("A","W")*self.iota(var,"A")*self.map("W","A")
            self.__i[(model, var)] = simpl_morphism(f)

        return self.__i[(model,var)]

    @cached_method
    def tau(self, model="A"):
        r'''
            Method to compute the map `\tau` over the kernel curve.

            The map `\tau` is the composition of the maps `\iota_2 \circ \iota_1` (see method :func:`iota`). This
            maps, when the kernel curve is smooth (see method :func:`is_singular`) is a birational map within
            the curve.

            This map computes the map `\tau` and simplifies the result.

            INPUT:
                * ``model``: model of the elliptic curve we work on. See method :func:`model` for further information.

            OUTPUT:
                * The map `\tau` in the representation requested by the argument ``model``.

            EXAMPLES::

                sage: from daeg1 import * 
                sage: WalkModel.example_model().tau('p')
                Scheme endomorphism of Closed subscheme of Product of projective spaces P^1 x P^1 ...
                (-t)*x0*x1*y0^2 + (-t)*x0^2*y0*y1 + x0*x1*y0*y1 + (-t)*x1^2*y0*y1 + (-t)*x0*x1*y1^2
                Defn: Defined by sending (x0 : x1 , y0 : y1) to 
                        (-x1 : -x0 , -y1 : -y0).
                sage: WalkModel.example_model().tau('a')
                Scheme endomorphism of Closed subscheme of Projective Space of dimension 2 ...
                (-t)*x^2*y + (-t)*x*y^2 + x*y*z + (-t)*x*z^2 + (-t)*y*z^2
                Defn: Defined on coordinates by sending (x : y : z) to
                        (-y*z : -x*z : -x*y)

            If a model is not elliptic (see method :func:`is_elliptic`), the method raise a :class:`NonEllipticError` when 
            asking for Weierstrass representation::

                sage: NonEllipticC[0].tau('p')
                Scheme endomorphism of Closed subscheme of Product of projective spaces P^1 x P^1 ...
                (-t)*x0*x1*y0^2 + (-t)*x1^2*y0^2 + x0*x1*y0*y1 + (-t)*x0^2*y1^2
                Defn: Defined by sending (x0 : x1 , y0 : y1) to 
                        (-x0^3*y1^2 : -x0^2*x1*y0^2 + (-2)*x0*x1^2*y0^2 - x1^3*y0^2 , -x0^2*y1 : -x0*x1*y0 - x1^2*y0).
                sage: NonEllipticC[0].tau('w')
                Traceback (most recent call last):
                ...
                NonEllipticError: The kernel is not a elliptic curve --> No Weierstrass model
        '''
        return simpl_morphism(self.iota('y',model)*self.iota('x',model))

    @cached_method
    def itau(self, model="A"):
        r'''
            Method to compute the map `\tau^{-1}` over the kernel curve.

            The map `\tau` is the composition of the maps `\iota_2 \circ \iota_1` (see method :func:`iota`). This
            maps, when the kernel curve is smooth (see method :func:`is_singular`) is a birational map within
            the curve.

            This map computes the map `\tau^{-1} = \iota_1 \circ \iota_2` and simplifies the result.

            INPUT:
                * ``model``: model of the elliptic curve we work on. See method :func:`model` for further information.

            OUTPUT:
                * The map `\tau^{-1}` in the representation requested by the argument ``model``.

            EXAMPLES::

                sage: from daeg1 import * 
                sage: WalkModel.example_model().itau('p')
                Scheme endomorphism of Closed subscheme of Product of projective spaces P^1 x P^1 ...
                (-t)*x0*x1*y0^2 + (-t)*x0^2*y0*y1 + x0*x1*y0*y1 + (-t)*x1^2*y0*y1 + (-t)*x0*x1*y1^2
                Defn: Defined by sending (x0 : x1 , y0 : y1) to 
                        (-x1 : -x0 , -y1 : -y0).
                sage: WalkModel.example_model().itau('a')
                Scheme endomorphism of Closed subscheme of Projective Space of dimension 2 ...
                (-t)*x^2*y + (-t)*x*y^2 + x*y*z + (-t)*x*z^2 + (-t)*y*z^2
                Defn: Defined on coordinates by sending (x : y : z) to
                        (-y*z : -x*z : -x*y)

            If a model is not elliptic (see method :func:`is_elliptic`), the method raise a :class:`NonEllipticError` when 
            asking for Weierstrass representation::

                sage: NonEllipticC[0].itau('p')
                Scheme endomorphism of Closed subscheme of Product of projective spaces P^1 x P^1 ...
                (-t)*x0*x1*y0^2 + (-t)*x1^2*y0^2 + x0*x1*y0*y1 + (-t)*x0^2*y1^2
                Defn: Defined by sending (x0 : x1 , y0 : y1) to 
                        (-x1*y0^2 : -x0*y1^2 , -x1^2*y0^3 : -x0*x1*y0^2*y1 - x0^2*y1^3).
                sage: NonEllipticC[0].itau('w')
                Traceback (most recent call last):
                ...
                NonEllipticError: The kernel is not a elliptic curve --> No Weierstrass model
        '''
        return simpl_morphism(self.iota('x',model)*self.iota('y',model))

    @cached_method
    def get_point_tau(self, model="P"):
        r'''
            Method to compute a point `Q` that represents the map `\tau`.

            In the particular case where the kernel curve is elliptic (see method :func:`is_elliptic`)
            then the map `\tau` (see method :func:`tau`) can be seen as the addition of a point `Q` from
            the elliptic curve:

            .. MATH::

                \tau(P) = P \oplus Q

            This method computes this point `Q`. For doing so, this method computes `\tau(O)` where `O` is 
            the neutral point of the elliptic curve.

            INPUT:
                * ``model``: model of the elliptic curve we work on. See method :func:`model` for further information.

            OUTPUT:
                * The point `Q` such that for all other points in the kernel curve `P`, `\tau(P) = P \oplus Q`.
                * If the model is not elliptic, a :class:`NonEllipticError` is raised.

            TODO: 
                * Add examples
        '''
        OP = self.neutral_point('P')

        tauP = apply_map(self.tau('P'), OP)
        model = self.model(model)

        return tauP if (model == "P") else apply_map(self.map('P', model), tauP)

    @cached_method
    def order_tau(self, bound = 10):
        r'''
            Method to compute the order of the map `\tau`.

            See method :func:`tau` to se information about the map `\tau`. This method tries to compute the order of the morphism
            `\tau` up to some bound order given by de user (`10` by default). 

            In the case that the kernel curve is elliptic (see method :func:`is_elliptic`), this order can be computed
            just taking a point on the curve (like the neutral point `O` - see method :func:`neutral_point`) and checking

            .. MATH::

                \tau^n(O) = O

            Otherwise, this method relies on the method :func:`~daeg1.algeo.order_morphism`.

            INPUT:
                * ``bound``: the bound for looking for the order.
            
            OUTPUT:
                * If the order of `\tau` is smaller or equal to ``bound`` then the method returns the order of `\tau`.
                * Otherwise, the method returns `\infty`.

            EXAMPLES::

                sage: daeg1 import * 
                sage: WalkModel.example_model().order_tau()
                2

            The bound argument put a limit on where we look for the order::

                sage: dic_models["FG-BMM-3.2"].order_tau()
                4
                sage: dic_models["FG-BMM-3.2"].order_tau(2)
                Infinity

            For the models in ``AllModels`` we can check all the orders of `\tau`::

                sage: all(m.order_tau() == 2 for m in AllModels if m.name().startswith("FG-BMM-1.")) # long time
                True
                sage: all(m.order_tau() == 3 for m in AllModels if m.name().startswith("FG-BMM-2.")) # long time
                True
                sage: dic_models["FG-BMM-3.1"].order_tau()
                4
                sage: dic_models["FG-BMM-3.2"].order_tau()
                4
                sage: all(m.order_tau() == Infinity for m in AllModels if not m.name().startswith("FG")) # long time
                True

        '''
        if(self.is_elliptic()):
            O = self.neutral_point("P")
            order = 1; current = apply_map(self.tau('P'), O)
            while(current != O and order <= bound):
                current = apply_map(self.tau('P'), current)
                order += 1

            if(order > bound):
                return Infinity
            return order
        return order_morphism(self.tau('P'), bound)

    def solve_finite_order_tau(self, order):
        r'''
            Method to get the values of the parameter to get finite order on `\tau`.

            The method `\tau` defined over the algebraic curve of the model have sometimes
            a finite order and, in other ocasions, infinite order. 
            However, these computations are generic, i.e., we compute the order of `\tau`
            independently of the value of the parameter `t`. It could happen that there are
            some values of the parameter `t` that changes the order of `\tau` (namely, it may
            be smaller).

            This method computes, fixed a defined order, the values of `t` that makes the map
            `\tau` have the corresponding order.

            INPUT:
                * ``order``: positive integer to set the order we are looking into.

            OUTPUT:
                The output of this method is the result of the Sage method ``solve`` over a list
                of expressions.
            
            EXAMPLE::
                
                sage: from daeg1 import *
                sage: m = EllipticC[0]; m
                Walk Model (wIA.01)
                sage: m.solve_finite_order_tau(1)
                []
                sage: m.solve_finite_order_tau(2)
                []
                sage: m.solve_finite_order_tau(3)
                [[t == 0]]
                sage: m.solve_finite_order_tau(4)
                [[t == 1/4*I*sqrt(3) - 1/4], 
                 [t == -1/4*I*sqrt(3) - 1/4], 
                 [t == 1/4*I*sqrt(3) + 1/4], 
                 [t == -1/4*I*sqrt(3) + 1/4]]         

            If the values of `t` are generic (i.e., the generic group is finite) this method returns ["all"] in 
            the appropriate orders::

                sage: m = FiniteGroup[0]; m
                Walk Model (FG-BMM-1.01)
                sage: m.solve_finite_order_tau(2)
                ['all']
                sage: m.solve_finite_order_tau(3)
                []

            For non-elliptic models (i.e., singular models) we do not perform any computation and 
            a NonEllipticError is raised::

                sage: m = NonEllipticC[0]; m
                Walk Model (NE-DHRS-1)
                sage: m.solve_finite_order_tau(2)
                Traceback (most recent call last):
                ...
                NonEllipticError: the model Walk Model (NE-DHRS-1) is not elliptic
        '''
        from sage.all import solve, var

        if(not self.is_elliptic()):
            raise NonEllipticError("the model %s is not elliptic" %self)

        P = self.neutral_point('p')
        Ox = P[0]; Oy = P[1]
        for _ in range(order): P = apply_map(self.tau('p'), P)
        Px = P[0]; Py = P[1]
        T = var('_t')
        system = []
        if(Ox[0] == 0):
            system += [Px[0](t=T)]
        elif(Ox[1] == 0):
            system += [Px[1](t=T)]
        else:
            try:
                system += [(Px[0]/Px[1] - Ox[0]/Ox[1])(t=T)]
            except ArithmeticError: #Px[1] = 0 --> It can not be
                return []
        if(Oy[0] == 0):
            system += [Py[0](t=T)]
        elif(Oy[1] == 0):
            system += [Py[1](t=T)]
        else:             
            try:                                  
                system += [(Py[0]/Py[1] - Oy[0]/Oy[1])(t=T)]
            except ArithmeticError: #Py[1] = 0 --> It can not be
                return []
        solutions = solve(tuple(system), T)
        if(len(solutions) > 0):
            if(any(not el.is_constant() for el in [sol[0].operands()[1] for sol in solutions])):
                return ["all"]
            return [[el(**{str(T):t}) for el in expression] for expression in solve(tuple(system), T)]
        return []

    @cached_method
    def b(self, var):
        if(str(var) == "x" or var == 1):
            var = 1
        elif(str(var) == "y" or var == 2):
            var = 2
        if(not (var in self.__b)):
            x,y,_ = self.vars("A")
            x0,x1,y0,y1 = self.vars("P")

            tau = pullback(self.tau("P"))

            px = (tau(x0/x1))(x0=x,x1=1,y0=y,y1=1)
            py = (tau(y0/y1))(x0=x,x1=1,y0=y,y1=1)

            self.__b[1] = py*(px-x)
            self.__b[2] = x*(py-y)

        return self.__b[var]

    ##########################################################################################
    ## Differential methods
    @cached_method
    def dy_dx(self):
        r'''
            Method that computes the relation between differentials on the Affine Curve `dy/dx`.

            See method :func:`derivative` for further information about the derivation in the 
            kernel curve (see method :func:`curve`).

            For any algebraic curve `K(x,y) = 0`, we do not only have a relation for the points
            but also an inherited relation between 1-forms:

            .. MATH::

                K_x(x,y) dx + K_y(x,y)dy = 0

            Then, for any curve we can compute the *derivation of* `y` *w.r.t.* `x`, i.e., the 
            quotient `dy/dx`:

            .. MATH::
            
                \frac{dy}{dx} = - \frac{K_x(x,y)}{K_y(x,y)}

            EXAMPLES::

                sage: from daeg1 import *
                sage: WalkModel.example_model().dy_dx()
                (2*t*x*y + t*y^2 - y + t)/((-t)*x^2 + (-2*t)*x*y + x - t)

            This quotient can also be computed even when the model is not elliptic::

                sage: NonEllipticC[0].dy_dx()
                (t*y^2 + 2*t*x - y)/((-2*t)*x*y + x + (-2*t)*y)
        '''
        x,y,_ = self.vars("A")
        k = self.kernel("A")(z=1)

        return -k.derivative(x)/k.derivative(y)

    @cached_method
    def dx_dy(self):
        r'''
            Method that computes the relation between differentials on the Affine Curve `dx/dy`.

            See method :func:`derivative` for further information about the derivation in the 
            kernel curve (see method :func:`curve`).

            For any algebraic curve `K(x,y) = 0`, we do not only have a relation for the points
            but also an inherited relation between 1-forms:

            .. MATH::

                K_x(x,y) dx + K_y(x,y)dy = 0

            Then, for any curve we can compute the *derivation of* `x` *w.r.t.* `y`, i.e., the 
            quotient `dx/dy`:

            .. MATH::
            
                \frac{dx}{dy} = - \frac{K_y(x,y)}{K_x(x,y)}

            EXAMPLES::

                sage: from daeg1 import *
                sage: WalkModel.example_model().dx_dy()
                (t*x^2 + 2*t*x*y - x + t)/((-2*t)*x*y + (-t)*y^2 + y - t)

            This quotient can also be computed even when the model is not elliptic::

                sage: NonEllipticC[0].dx_dy()
                (2*t*x*y - x + 2*t*y)/((-t)*y^2 + (-2*t)*x + y)

            This method always returns the multiplicative inverse of the method :func:`dy_dx`::

                sage: all(1/m.dx_dy() == m.dy_dx() for m in AllModels)
                True
        '''
        x,y,_ = self.vars("A")
        k = self.kernel("A")(z=1)

        return -k.derivative(y)/k.derivative(x)

    @cached_method
    def holomorphic_form(self, model="A"):
        r'''
            Method that computes the _unique_ holomorphic form on the elliptic curve.

            This method computes a holomorphic differential form on the elliptic curve defined in the model.
            On an elliptic curve there is a unique (up to constant) holomorphic form. If the curve is on the
            Weierstrass model, such form is `(du)/v`. This form defines a unique derivation on the elliptic curve
            that allows to compute some differential operator that, in the end, will commute with the
            isomorpism `\tau` defined by the method :func:`tau`.

            For the model in the coordinates `x`, `y` and `z` (see method :func:`model` for more information) this
            form can be computed quickly since we have `u = u(x,y,z)`, `v = v(x,y,z)` and then

            .. MATH::

                du = u_x dx + u_y dy + u_z dz.

            INPUT:
                * ``model``: the model we want to compute the holomorphic form (see :func:`model`). The double
                  projective model (i.e., ``P``) is not implemented.

            OUTPUT:
                * A pair `(f,g)` rational function on the model given such that the holomorphic form is `\omega = fdx + gdy`
                  where `x` and `y` are the two affine variables of the model.
                * If the kernel curve is not elliptic (see method :func:`is_elliptic`) a :class:`NonEllipticError` is raised.

            EXAMPLES::

                sage: from daeg1 import *
                sage: m = NonEllipticC[0]; m.holomorphic_form()
                Traceback (most recent call last):
                ...
                NonEllipticError: The kernel is not a elliptic curve --> No Weierstrass model

            TODO:
                * Increase the number of tests
        '''
        model = self.model(model)
        u,v,w = self.vars("W")
        if(model == "W"):
            return (1/v,0)
        elif(model == "A"):
            from_E_to_W = pullback(self.map("A", "W"))

            pu = from_E_to_W(u/w)(z=1)
            pv = from_E_to_W(v/w)(z=1)

            x,y,_ = self.vars(model)
            return (pu.derivative(x)/pv, pu.derivative(y)/pv)
        else:
            return NotImplemented

    @cached_method
    def dx(self):
        r'''
            Method to compute the 1-form `dx` w.r.t the holomorphic form.

            On an elliptic curve there is a unique (up to constant) holomorphic form `\omega` (see method :func:`holomorphic_form`).
            Then all 1-forms can be written as `\omega` multiplied by a rational function. This method computes
            
            .. MATH::
                
                dx = F \omega

            and returns the rational function `F` that represents `dx` w.r.t. `\omega`.

            OUTPUT:
                * The rational function `F` such that `dx = F\omega`.
                * If the kernel curve is not elliptic (see method :func:`is_elliptic`) a :class:`NonEllipticError` is raised.

            EXAMPLES::

                sage: from daeg1 import *
                sage: m = NonEllipticC[0]; m.dx()
                Traceback (most recent call last):
                ...
                NonEllipticError: The kernel is not a elliptic curve --> No Weierstrass model

            TODO:
                * Increase the number of tests
        '''
        fx,fy = self.holomorphic_form()
        f = fx + fy*self.dy_dx()

        return simplify_rational_variety(1/f, self.map('a','w').domain())(z=1)

    @cached_method
    def dy(self):
        r'''
            Method to compute the 1-form `dy` w.r.t the holomorphic form.

            On an elliptic curve there is a unique (up to constant) holomorphic form `\omega` (see method :func:`holomorphic_form`).
            Then all 1-forms can be written as `\omega` multiplied by a rational function. This method computes
            
            .. MATH::
                
                dy = G \omega

            and returns the rational function `G` that represents `dy` w.r.t. `\omega`.

            OUTPUT:
                * The rational function `G` such that `dy = G\omega`.
                * If the kernel curve is not elliptic (see method :func:`is_elliptic`) a :class:`NonEllipticError` is raised.

            EXAMPLES::

                sage: from daeg1 import *
                sage: m = NonEllipticC[0]; m.dy()
                Traceback (most recent call last):
                ...
                NonEllipticError: The kernel is not a elliptic curve --> No Weierstrass model

            TODO:
                * Increase the number of tests
        '''
        fx,fy = self.holomorphic_form()
        f = fy + fx*self.dx_dy()

        return simplify_rational_variety(1/f, self.map('a','w').domain())(z=1)

    @dLogFunction
    def derivative(self, f, model="A"):
        r'''
            Method for computing the derivative of a rational function over the curve.

            This method takes a rational function on 'x' and 'y' coordinates and computes the corresponding
            derivation that commutes with the morphism '\tau'. It is important that the function
            does not involve the variable 'z'.

            Vefore returning, it uses the equation of the curve to simplify the resulting function.
        '''
        model = self.model(model)

        if(model == "A"):
            x,y,_ = self.vars("A")
            return simplify_rational_variety(f.derivative(x)*self.dx() + f.derivative(y)*self.dy(), self.map('a','w').domain())(z=1)
        elif(model == "P"):
            x,y,_ = self.vars("A")
            x0,x1,y0,y1 = self.vars("P")
            return self.derivative(f(x0=x,x1=1,y0=y,y1=1))(x=x0/x1,y=y0/y1)
        elif(model == "W"):
            pUtX = pullback(self.map("W","A")); pXtU = pullback(self.map("A","W"))
            return simplify_rational_variety(pUtX(self.derivative(pXtU(f))), self.map('a','w').codomain())
        else:
            raise TypeError("WalkModel:derivative: model not recognized")

    ##########################################################################################
    ## Private methods
    @dLogFunction
    def __get_maple_info(self, name="r"):
        if(not name in self.__maple):
            from sage.interfaces.maple import maple
            R_UVW = self.ring('W'); F_UVW = R_UVW.fraction_field()
            R_XYZ = self.ring('A'); F_XYZ = R_XYZ.fraction_field()
            u,v,w = self.vars('W')
            x,y,z = self.vars('A')

            ## Using Maple to get nicer mappings to Weierstrass form
            maple.restart()
            _ = maple("assign(('eqWF', 'U', 'V', 'X', 'Y')=op(algcurves[Weierstrassform](%s, %s, %s, %s, %s, Weierstrass)))" %(self.kernel("A")(z=1),x,y,u,v))
            U = maple.get("U"); V = maple.get("V"); X = maple.get("X"); Y = maple.get("Y"); new_eq = maple.get("eqWF")

            ## At this point we have strings with the result of the Maple computation.
            ## Getting the algebraic elements
            algebraic_equations = list(set([el.split(")")[0] for el in sum([line.split("RootOf(")[1:] for line in [U,V,X,Y,new_eq]], [])]))
            if(len(algebraic_equations) > 0):
                base_field = R_UVW.base_ring()
                if(len(algebraic_equations) > 1): # Case with multiple algebraic extensions
                    dlogging.warning("WalkModel:GMI: more than one algebraic extension")
                    i = 0
                    for equation in algebraic_equations:
                        new_name = name+("_%d" %i)
                        poly = PolynomialRing(base_field, name)(equation.replace("_Z", name))
                        F, roots, _ = self.alg_extension(poly, new_name); element = roots[0]

                        U,V,X,Y,new_eq = [el.replace("RootOf(%s)" %equation, str(element)) for el in [U,V,X,Y,new_eq]]

                elif(len(algebraic_equations) == 1): # Case with only one algebraic extension
                    poly = PolynomialRing(base_field, name)(algebraic_equations[0].replace("_Z", name))
                    F, roots, _ = self.alg_extension(poly, name); element = roots[0]
                    
                    U,V,X,Y,new_eq = [el.replace("RootOf(%s)" %algebraic_equations[0], str(element)) for el in [U,V,X,Y,new_eq]]

                R_UVW = R_UVW.change_ring(F); F_UVW = FractionField(R_UVW)
                u,v,w = [R_UVW(el) for el in [u,v,w]]
                R_XYZ = R_XYZ.change_ring(F); F_XYZ = FractionField(R_XYZ)
                x,y,z = [R_XYZ(el) for el in [x,y,z]]
            else:
                F = R_UVW.base_ring()

            U = F_XYZ(U); V = F_XYZ(V); X = F_UVW(X); Y = F_UVW(Y); new_eq = R_UVW(new_eq)

            ## Creating the corresponding maps
            U = U(x=x/z,y=y/z); V = V(x=x/z, y=y/z)
            try:
                g_W = gcd(U.denominator(), V.denominator())
                lcm_W = R_XYZ(U.denominator()*V.denominator()//g_W)
                factor_U = R_XYZ(V.denominator()//g_W); factor_V = R_XYZ(U.denominator()//g_W)
            except NotImplementedError:
                lcm_W = U.denominator()*V.denominator()
                factor_U = V.denominator(); factor_V = U.denominator()

            X = X(u=u/w,v=v/w); Y = Y(u=u/w, v=v/w)
            try:
                g_A = gcd(X.denominator(), Y.denominator())
                lcm_A = R_UVW(X.denominator()*Y.denominator()//g_A)
                factor_X = R_UVW(Y.denominator()//g_A); factor_Y = R_UVW(X.denominator()//g_A)
            except NotImplementedError:
                lcm_A = X.denominator()*Y.denominator()
                factor_X = Y.denominator(); factor_Y = X.denominator()

            UVW = tuple([R_XYZ(el) for el in (U.numerator()*factor_U, V.numerator()*factor_V, lcm_W)])
            XYZ = tuple([R_UVW(el) for el in (X.numerator()*factor_X, Y.numerator()*factor_Y, lcm_A)])

            new_eq = self.ring('W')(str(R_UVW(new_eq).homogenize(w)))
            self.__kernel['W'] = self.ring('W')(str(new_eq))

            ## Assigning the result to the variables of the Model

            if(WalkModel._F != F): #self.change_ring(F)
                ## Creating extended curves
                self.__maps[('W','A')] = simpl_morphism(Hom(self.curve('W').change_ring(F), self.curve('A').change_ring(F))(XYZ))
                self.__maps[('A','W')] = simpl_morphism(Hom(self.curve('A').change_ring(F), self.curve('W').change_ring(F))(UVW))
                self.__maps[('A','P')] = self.map('A','P').change_ring(F)
                self.__maps[('P','A')] = self.map('P','A').change_ring(F)
            else:
                self.__maps[('W','A')] = simpl_morphism(Hom(self.curve('W'), self.curve('A'))(XYZ))
                self.__maps[('A','W')] = simpl_morphism(Hom(self.curve('A'), self.curve('W'))(UVW))

            self.__maple[name] = (UVW,XYZ,new_eq)
        return self.__maple[name]

    @dLogFunction
    def alg_extension(self, polynomial, n=None):
        r'''
            Method to compute a uniform algebraic extension through all computations in the model.

            This method allows the user to compute an algebraic extension with an uniform criteria
            through all computations. In this way, we will end up always with the smallest amount
            of extensions and, if possible, with **the same** extension through all the computations.

            INPUT:
                * ``polynomial``: a polynomial in one variable.
                * ``n``: name for the algebraic extension. If not given, a standar decision for the name will be made.
        '''
        if(n is None):
            name = str(chr(self.__nextensions + ord('a')))
        else:
            name = n
        F = self.__field_F; G = self.__field_G
        Ft = FractionField(PolynomialRing(F, self.pars()))
        polynomial = polynomial.change_ring(G); y = polynomial.parent().gens()[0]
        if(polynomial.degree() == 0): # Constant polynomial --> no roots
            return G, [], 0
        elif(polynomial.degree() == 1): # linear polynomial --> no extenstions, 1 root
            return G, [-polynomial[0]/polynomial[1]], 0
        
        ## Generic case: dergee of polynomial >= 2
        nF = F; nG = G; elements = []; nextensions = 0
        if(all(el in F for el in polynomial.coefficients())): # The extension is over the field F only
            nF, roots, next_F = self.__alg_before_t(polynomial, name)
            elements = [str(root) for root in roots]
            nextensions += next_F
        else:
            try:
                polynomial = polynomial.change_ring(Ft)
                d = polynomial.degree(); t = self.pars().numerator()
                if(polynomial[d] != 1): polynomial /= polynomial[d]
                g = polynomial[0]; n = g.numerator().degree()
            except:
                d = 2; g = 1/self.pars().numerator(); n = 1
                t = self.pars().numerator()
            if(all([
                all(el == 0 for el in [polynomial[i] for i in range(1, d)]),
                g.denominator().is_constant(),
                n%d == 0,
                (t**n).divides(g.numerator()) in F])
            ): # polynomial = y^d + t^{nd}g
                g = g//(t**n)
                nF, roots, next_F = self.__alg_before_t(y**d + g, name)
                elements = ["%s**%s * %s" %(t, n//d, root) for root in roots]
                nextensions += next_F
            else:
                ## Treating the name of the algebraic extension
                spl_name = name.split("_"); num = 0
                try:
                    num = int(spl_name[-1])
                    new_name = "_".join(spl_name[:-1])
                except:
                    new_name = name

                ## Computing the algebraic extension iteratively
                nG = G.extension(polynomial, new_name+"_%d" %num); self.__field_G = nG; a = nG(new_name+"_%d" %num)

                nG, other_roots, next_G = self.alg_extension(polynomial.change_ring(nG)//(y.change_ring(nG)- a), new_name+"_%d" %(num+1))
                elements = [str(a)] + [str(root) for root in other_roots]
                nextensions += 1 + next_G
                
        if(nF != F): # Updating the field F if necessary
            self.__field_F = nF
            ## This change implies changes on G
            const = []; current_G = G
            while(current_G != Ft):
                const += (current_G.construction()[0].I.gens()[0], current_G.construction()[0].names[0]) # (polynomial, name) for extension
                current_G = current_G.base_ring()
            const.reverse()

            current_G = FractionField(PolynomialRing(nF, self.pars()))
            for el in const:
                current_G = current_G.extension(el[0].change_ring(current_G), el[1])
            nG = current_G
        if(nG != G): # Updating the field G if neccessary
            self.__field_G = nG

        if(nextensions > 0): self.__nextensions += 1

        return self.__field_G, [self.__field_G(element) for element in elements], nextensions

    def __alg_before_t(self, polynomial, name):
        F = self.__field_F; y = polynomial.parent().gens()[0]
        polynomial = PolynomialRing(F, y)(str(polynomial))
        if(polynomial.degree() == 0):
            return F, [], 0
        elif(polynomial.is_irreducible()):
            if(polynomial.degree() == 1):
                return F, [-polynomial[0]/polynomial[1]], 0
            elif(all(polynomial[i] == 0 for i in range(1, polynomial.degree())) and polynomial[0]/polynomial[polynomial.degree()] == 1): # polynomial = ax^d + a
                if(polynomial.degree() == 2): name = "i" # the usual imaginary number
                else: name = "ur_%d" %polynomial.degree() # a primitive d-root of unity

                F_ext = F.extension(polynomial, name) # extending the field
                self.__field_F = F_ext

                return F_ext, [F_ext(name)**i for i in range(1,polynomial.degree()+1)], 1
            elif(polynomial.degree() == 2):
                F_ext = F.extension(polynomial, name)
                self.__field_F = F_ext
                
                return F_ext, [F_ext(name), F_ext(-polynomial[1]/polynomial[2])-F_ext(name)], 1
            else:
                ## Treating the name of te algebraic extension
                spl_name = name.split("_"); num = 0
                try:
                    num = int(spl_name[-1])
                    new_name = "_".join(spl_name[:-1])
                except:
                    new_name = name

                ## Computing the algebraic extension iteratively
                F_ext = F.extension(polynomial, new_name+"_%d" %num); self.__field_F = F_ext; a = F_ext(new_name+"_%d" %num)

                F_ext, other_roots, nextensions = self.__alg_before_t(polynomial//(F_ext(y)- a), new_name+"_%d" %(num+1))
                return F_ext, [a] + other_roots, nextensions + 1
        else: # the polynomial is not irreduccible
            ## Treating the name of te algebraic extension
            spl_name = name.split("_"); num = 0
            try:
                num = int(spl_name[-1])
                new_name = "_".join(spl_name[:-1])
            except:
                new_name = name

            ## Computing the algebraic extenstions
            factors = [factor[0] for factor in polynomial.factor()]; factors.sort(key=lambda p : p.degree(), reverse=True)
            roots = []; nex = 0
            for factor in factors:
                F_ext, more_roots, nextensions = self.__alg_before_t(factor, new_name + "_%d" %(num+nex))
                nex += nextensions
                roots += more_roots
            return F_ext, roots, num

    ##########################################################################################
    ## Magic methods of the Model:
    def __str__(self):
        if(self.__name is None):
            return "Walk Model with steps: " + ", ".join([str(el) for el in self.steps()])
        else:
            return "Walk Model (%s)" %self.__name

    def __repr__(self):
        return self.__str__()

    def __hash__(self):
        return hash(self.kernel())

    def __contains__(self, step):
        return any(step == el[0] for el in self.steps() if el[1] != 0)

    def __eq__(self, other):
        if(isinstance(other, WalkModel)):
            return self.step() == other.step()
        return False
    ##########################################################################################
    ## Visualizing method
    def plot(self):
        r'''
            Method to plot the valid steps for a model.

            This method creates a plot Sage image that displays with blue arrows the 
            valid steps of this model. It is important to remark that currently this 
            depiction of the model does not include the weights of the given steps.
        '''
        from sage.plot.arrow import arrow

        picture = sum(arrow((0,0), P) for P in self.__steps)
        picture.set_axes_range(-1,1,-1,1)
        picture.set_aspect_ratio(1)
        return picture

    def plot_walk(self, size, start=(0,0), restriction="quarter", **kwds):
        '''
            This method depicts a random walk valid for this model.

            This method creates a random walk valid for the model (see method :func:`random_walk`). The picture
            prints with arrows all the middle steps and make a transition in colors from the beginning of the
            walk until the end.

            INPUT::
                * ``size``: number of steps of the random walk.
                * ``start``: starting point for the generated random walk.
                * ``restriction``: restriction for the random walk (see :func:`random_walk`)
                * ``kwds``: this method allows extra parameters:
                    * ``init_color``: a valid input for ``rgbcolor``. This will be the color from the beginning of the walk.
                      This value is set to ``"blue"`` by default.
                    * ``end_color``: a valid input for ``rgbcolor``. This will be the color from the beginning of the walk.
                      This value is set to ``"red"`` by default.
        '''
        from sage.plot.arrow import arrow
        from sage.plot.colors import rgbcolor
        _,steps = self.random_walk(size, start, True, restriction)

        ## Defining the colors for the arrows
        init_color = rgbcolor(kwds.get('init_color', "blue"), 'rgb')
        end_color = rgbcolor(kwds.get('end_color', "red"), 'rgb')
        def get_color(it):
            pos = float(it)/(size-1)
            return rgbcolor(tuple((1-pos)*init_color[i] + pos*end_color[i] for i in range(3)), 'rgb')

        result = arrow(start, steps[0],color=init_color); current = tuple(start[j]+steps[0][j] for j in range(2))

        ## Building the arrows
        for i in range(1,len(steps)):
            next = tuple(current[j]+steps[i][j] for j in range(2))
            result += arrow(current, next, color=get_color(i))
            current = next

        ## Configuring the aspect of the plot
        result.set_aspect_ratio(1)

        ## Return
        return result

    def name(self):
        r'''
            Method to recover the name for the model.

            This method returns the name (if stablished) for this model. If there is no name set, then
            this method returns an empty string.

            EXAMPLES::

                sage: from daeg1 import *
                sage: WalkModel.example_model().name()
                Example Model
                sage: AllModels[0]
                FG-BMM-1.01
            
            It is important to remark that having different names does not imply that the models are different::

                sage: AllModels[0] == WalkModel.example_model()
                True
                sage: AllModels[0].name() == WalkModel.example_model().name()
                False
        '''
        if(self.__name is None): return ""

        return self.__name

##########################################################################################
## Defining the small steps
N = WalkModel.N; S = WalkModel.S; E = WalkModel.E; W = WalkModel.W
NE = WalkModel.NE; NW = WalkModel.NW; SE = WalkModel.SE; SW = WalkModel.SW
small_steps = WalkModel.small_steps

## Defining particular Walk Models
KingModel = WalkModel(N,NE,E,SE,S,SW,W,NW, name="King model")
RookModel = WalkModel(N,S,E,W, name="Rook model")

## Defining models from papers
# Finite group
AlgebraicGF=[
    WalkModel(NE,S,W, name="AGF-BBMR-1"),
    WalkModel(N,E,SW, name="AGF-BBMR-2"),
    WalkModel(N,NE,E,S,SW,W, name="AGF-BBMR-3"),
    WalkModel(NE,E,SW,W, name="AGF-BBMR-4")
]

FiniteGroup = [
    WalkModel(N,E,S,W, name="FG-BMM-1.01"),
    WalkModel(NE,SE,SW,NW, name="FG-BMM-1.02"),
    WalkModel(N,NE,SE,S,SW,NW, name="FG-BMM-1.03"),
    WalkModel(N,NE,E,SE,S,SW,W,NW, name="FG-BMM-1.04"),
    WalkModel(NE,S,NW, name="FG-BMM-1.05"),
    WalkModel(NE,E,S,W,NW, name="FG-BMM-1.06"),
    WalkModel(N,NE,S,NW, name="FG-BMM-1.07"),
    WalkModel(N,NE,E,S,W,NW, name="FG-BMM-1.08"),
    WalkModel(N,NE,SE,SW,NW, name="FG-BMM-1.09"),
    WalkModel(N,NE,E,SE,SW,W,NW, name="FG-BMM-1.10"),
    WalkModel(N,SE,S,SW, name="FG-BMM-1.11"),
    WalkModel(N,E,SE,S,SW,W, name="FG-BMM-1.12"),
    WalkModel(NE,SE,S,SW,NW, name="FG-BMM-1.13"),
    WalkModel(NE,E,SE,S,SW,W,NW, name="FG-BMM-1.14"),
    WalkModel(N,SE,SW, name="FG-BMM-1.15"),
    WalkModel(N,E,SE,SW,W, name="FG-BMM-1.16"),
    WalkModel(N,SE,W, name="FG-BMM-2.1"),
    WalkModel(N,E,SE,S,W,NW, name="FG-BMM-2.2"),
    WalkModel(NE,S,W, name="FG-BMM-2.3"),
    WalkModel(N,E,SW, name="FG-BMM-2.4"),
    WalkModel(N,NE,E,S,SW,W, name="FG-BMM-2.5"),
    WalkModel(E,SE,W,NW, name="FG-BMM-3.1"),
    WalkModel(NE,E,SW,W, name="FG-BMM-3.2")
]

DAModels = [
    WalkModel(N,S,E,SW, name="DA-BBMR-1"),
    WalkModel(N,E,SE,SW, name="DA-BBMR-2"),
    WalkModel(N,NE,S,W, name="DA-BBMR-3"),
    WalkModel(N,E,SE,W, name="DA-BBMR-4"),
    WalkModel(N,NE,E,SW,W, name="DA-BBMR-5"),
    WalkModel(N,NE,S,SW,W, name="DA-BBMR-6"),
    WalkModel(N,E,SE,S,SW, name="DA-BBMR-7"),
    WalkModel(N,NE,E,S,W, name="DA-BBMR-8"),
    WalkModel(N,E,SE,S,NW, name="DA-BBMR-9")
]

NonEllipticC = [
    WalkModel(N,SE,NW, name="NE-DHRS-1"),
    WalkModel(NE,SE,NW, name="NE-DHRS-2"),
    WalkModel(N,NE,SE,NW, name="NE-DHRS-3"),
    WalkModel(N,NE,E,SE,NW, name="NE-DHRS-4"),
    WalkModel(N,E,SE,NW, name="NE-DHRS-5")
]

EllipticC = [
    WalkModel([NE,SE,S,NW],name="wIA.01"),
    WalkModel([N,NE,SE,S,NW],name="wIA.02"),
    WalkModel([N,NE,SE,W,NW],name="wIA.03"),
    WalkModel([NE,SE,S,W,NW],name="wIA.04"),
    WalkModel([N,NE,E,SE,W,NW],name="wIA.05"),
    WalkModel([N,NE,E,SE,SW,NW],name="wIA.06"),
    WalkModel([N,NE,SE,S,W,NW],name="wIA.07"),
    WalkModel([NE,SE,S,SW,W,NW],name="wIA.08"),
    WalkModel([N,NE,E,SE,S,W,NW],name="wIA.09"),
    WalkModel([N,NE,SE,SW,W,NW],name="wIA.10"),
    WalkModel([NE,S,SW,NW],name="wIB.1"),
    WalkModel([NE,S,W,NW],name="wIB.2"),
    WalkModel([N,NE,S,SW,NW],name="wIB.3"),
    WalkModel([N,NE,S,W,NW],name="wIB.4"),
    WalkModel([NE,S,SW,W,NW],name="wIB.5"),
    WalkModel([N,NE,S,SW,W,NW],name="wIB.6"),
    WalkModel([N,NE,E,SW,NW],name="wIC.1"),
    WalkModel([N,NE,E,S,NW],name="wIC.2"),
    WalkModel([N,NE,E,S,SW,W,NW],name="wIC.3"),
    WalkModel([N,NE,SE,SW],name="wIIA.1"),
    WalkModel([N,NE,SE,W],name="wIIA.2"),
    WalkModel([N,NE,SE,SW,W],name="wIIA.3"),
    WalkModel([N,NE,SE,S,SW],name="wIIA.4"),
    WalkModel([N,NE,E,SE,S,SW],name="wIIA.5"),
    WalkModel([N,NE,E,SE,SW,W],name="wIIA.6"),
    WalkModel([N,NE,SE,S,SW,W],name="wIIA.7"),
    WalkModel([N,E,S,SW],name="wIIB.01"),
    WalkModel([N,E,SE,SW],name="wIIB.02"),
    WalkModel([N,E,SE,W],name="wIIB.03"),
    WalkModel([N,E,SE,S,W],name="wIIB.04"),
    WalkModel([N,E,S,SW,W],name="wIIB.05"),
    WalkModel([N,E,SE,S,SW],name="wIIB.06"),
    WalkModel([N,NW,S,SE,E],name="wIIB.07"),
    WalkModel([N,NW,SW,SE,E],name="wIIB.08"),
    WalkModel([N,NW,W,SW,SE,E],name="wIIB.09"),
    WalkModel([N,NW,W,SW,S,SE,E],name="wIIB.10"),
    WalkModel([N,NE,S,W],name="wIIC.1"),
    WalkModel([N,NE,S,SW,W],name="wIIC.2"),
    WalkModel([N,NE,E,SW],name="wIIC.3"),
    WalkModel([N,NE,E,SW,W],name="wIIC.4"),
    WalkModel([N,NE,E,S,W],name="wIIC.5"),
    WalkModel([N,W,S,SE],name="wIID.1"),
    WalkModel([N,W,SW,SE],name="wIID.2"),
    WalkModel([N,NW,SW,SE],name="wIID.3"),
    WalkModel([N,NW,W,SE],name="wIID.4"),
    WalkModel([N,W,SW,S,SE],name="wIID.5"),
    WalkModel([N,NW,SW,S,SE],name="wIID.6"),
    WalkModel([N,NW,W,S,SE],name="wIID.7"),
    WalkModel([N,NW,W,SW,SE],name="wIID.8"),
    WalkModel([N,NW,W,SW,S,SE],name="wIID.9"),
    WalkModel([NE,S,SW,W],name="wIII")
]

AllModels = FiniteGroup + NonEllipticC + EllipticC

dic_DHRS = {m.name() : m for m in AllModels if m in EllipticC}
dic_DA = {m.name() : m for m in EllipticC if m in DAModels}
dic_models = {m.name() : m for m in AllModels}

t = WalkModel.example_model().pars()
x,y,z = WalkModel.example_model().vars("A")
u,v,w = WalkModel.example_model().vars("W")
x0,x1,y0,y1 = WalkModel.example_model().vars("P")
