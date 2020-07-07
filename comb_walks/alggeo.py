r'''
    File for the general methods concerning Algebraic Geometry

    In this file we include several useful methods that can be written in a generic
    way involving reasoning over Algebraic Geometry. Our main concern will be
    Projective curves, although sometimes the methods will work with Affine varieties.

    This package is based on Sage implementation of Algebraic geometry such as
    subschemes, coordinate rings and morphism. For further information, look to
    the documentation of each particular method.

    AUTHORS:
        * Antonio Jimenez-Pastor (2020-04-11): initial version

    TODO: 
        * do the examples of the package

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

from sage.all import (FractionField, Hom, parent, gcd, prod, lcm, Infinity,
    reduce, PolynomialRing, cached_function)

import deprecation
from datetime import datetime

from . import dlogging
from .dlogging import dLogFunction

### Private methods for the module
def __default_algebraic_extension(field, polynomial, name):
    if(polynomial.degree() == 0):
        dlogging.info("alggeo:__DAE: constant polynomial --> no roots")
        return field, [], 0
    elif(polynomial.degree() == 1):
        dlogging.info("alggeo:__DAE: linear polynomial --> one root, no extension")
        return field, [-polynomial[0]/polynomial[1]], 0
    elif(polynomial.degree() == 2):
        dlogging.info("alggeo:__DAE: quadratic polynomial --> two roots, one extension")
        extension = field.extension(polynomial, name); a = extension(name)
        return extension, [a, -a - extension(polynomial[1]/polynomial[2])], 1
    else: # higher degree
        try:
            dlogging.warning("\n\t".join([
                "alggeo:__DAE: algebraic points of degree greater than 2 --> Need a splitting field",
                "- Polynomial: %s" %polynomial,
                "### MAY REQUIRE LONG TIME ###",
                "### Started: %s" %datetime.now().strftime("%H:%M:%S")]))
            splitting_field = polynomial.splitting_field(name)
            dlogging.warning("alggeo:__DAE: splitting field finally computed (Ended: %s)" %datetime.now().strftime("%H:%M:%S"))
            polynomial = polynomial.change_ring(splitting_field)
            return splitting_field, [-f[0][0]/f[0][1] for f in polynomial.factor()], 1
        except NotImplementedError: # splitting field not implemented
            dlogging.warning("alggeo:__DAE: splitting field not implemented.")
            dlogging.info("alggeo:__DAE: computing extensions iteratively")
            if(len(name.split("_")) == 1):
                name = name+"_0"; num = 0
            else:
                num = int(name.split("_")[-1])
            extension = field.extension(polynomial, name); a = extension(name)
            polynomial = polynomial.change_ring(extension)
            poly_parent = polynomial.parent(); y = poly_parent.gens()[0]
            # Recursive call removing the 
            new_name = "_".join(name.split("_")[:-1]) + "_%d" %(num+1)
            final_extension, roots, nextensions = __default_algebraic_extension(extension, polynomial//(y-a), new_name)

            dlogging.info("alggeo:__DAE: computed roots --> %d extensions" %nextensions)
            return final_extension, [a] + roots, (nextensions + 1)

### Public method for the module
def pullback(morphism, lift=True):
    r'''
        Method that takes a rational map between Projective varieties and returns its pullback.

        Given a rational map between two projectives varieties `\varphi: A \rightarrow B`, the pullback
        is defined as a map on the ring of rational functions over the varieties `C(A)` and `C(B)` defined
        as

        .. MATH::
            \varphi^* : C(B) \rightarrow C(A),

        such that for any point `P \in A`, `\varphi^*(f)(P) = f(\varphi(P))`, i.e., `\varphi(f) = f \circ \varphi`.

        The argument ``lift`` determines if the map is considered in the total ambient space or in the coordinate rings.

        EXAMPLES::

            sage: from comb_walks.alggeo import *
            sage: # Testing a pullback between the ambient spaces
            sage: D = ProjectiveSpace(2, QQ, 'xyz'); CD = ProjectiveSpace(2,QQ, 'uvw')
            sage: x,y,z = D.gens(); u,v,w = CD.gens()
            sage: h = Hom(D, CD)([x^2, y*z-x*z, y^2])
            sage: p = pullback(h); p
            Ring morphism:
              From: Fraction Field of Multivariate Polynomial Ring in u, v, w over Rational Field
              To:   Fraction Field of Multivariate Polynomial Ring in x, y, z over Rational Field
              Defn: u |--> x^2
                    v |--> -x*z + y*z
                    w |--> y^2
            sage: p(u)
            x^2
            sage: p(v)
            -x*z + y*z
            sage: p(w)
            y^2
            sage: # Testing a pullback between two curves
            sage: C1 = D.subscheme(x^2-z*y); # usual parabola
            sage: C2 = CD.subscheme(v); # the u axis
            sage: h = Hom(C2, C1)([u*w,u^2,w^2]); h # the vertical lifting
            Scheme morphism:
              From: Closed subscheme of Projective Space of dimension 2 over Rational Field defined by:
              v
              To:   Closed subscheme of Projective Space of dimension 2 over Rational Field defined by:
              x^2 - y*z
              Defn: Defined on coordinates by sending (u : v : w) to
                    (u*w : u^2 : w^2)
            sage: p = pullback(h); p
            Ring morphism:
              From: Fraction Field of Multivariate Polynomial Ring in x, y, z over Rational Field
              To:   Fraction Field of Multivariate Polynomial Ring in u, v, w over Rational Field
              Defn: x |--> u*w
                    y |--> u^2
                    z |--> w^2
            sage: p(x^2-y*z) == 0 # the pullback of the equation for C2 has to go to the zero element
            True
    '''
    codomain = morphism.codomain()
    domain = morphism.domain()
    if(lift): # If lifted, getting the ambient space
        codomain = codomain.ambient_space()
        domain = domain.ambient_space()

    cd_cring = codomain.coordinate_ring()
    d_cring = domain.coordinate_ring()

    if(lift): # If lifted, going to the rational functions
        cd_cring = FractionField(cd_cring)
        d_cring = FractionField(d_cring)

    H = Hom(cd_cring, d_cring)

    func = H([d_cring(p) for p in morphism.defining_polynomials()])

    return func

@dLogFunction()
def simpl_morphism(morphism):
    r'''
        Static method that simplifies a morphism between projectives varieties.

        This method reduces the gcd from the defining polynomials of the morphism provided.
        Since the map is between projective varieties, the map is defined up to a common factor between
        its coordinates. In fact, the bigger the number of common factors, the bigger the locus of
        indeterminacy of the map.

        Here we divide all the defining polynomials by the `gcd` and also try to recude the size of the content of those
        polynomials.

        EXAMPLES::

            sage: from comb_walks.alggeo import *
            sage: D = ProjectiveSpace(2, QQ, 'xyz'); CD = ProjectiveSpace(2,QQ, 'uvw')
            sage: x,y,z = D.gens(); u,v,w = CD.gens()
            sage: C1 = D.subscheme(x^2-z*y); # usual parabola
            sage: C2 = CD.subscheme(v); # the u axis
            sage: h = Hom(C1, C2)([el*3*(27*x-y+z) for el in [x, 0, z]])
            sage: h
            Scheme morphism:
              From: Closed subscheme of Projective Space of dimension 2 over Rational Field defined by:
              x^2 - y*z
              To:   Closed subscheme of Projective Space of dimension 2 over Rational Field defined by:
              v
              Defn: Defined on coordinates by sending (x : y : z) to
                    (81*x^2 - 3*x*y + 3*x*z : 0 : 81*x*z - 3*y*z + 3*z^2)
            sage: simpl_morphism(h)
            Scheme morphism:
              From: Closed subscheme of Projective Space of dimension 2 over Rational Field defined by:
              x^2 - y*z
              To:   Closed subscheme of Projective Space of dimension 2 over Rational Field defined by:
              v
              Defn: Defined on coordinates by sending (x : y : z) to
                    (x : 0 : z)

        The simplification can be done also when the image is a product of projective spaces::

            sage: P2 = ProjectiveSpace(1, QQ, 'x').cartesian_product(ProjectiveSpace(1, QQ, 'y'))
            sage: x0, x1, y0, y1 = P2.gens()
            sage: C3 = P2.subscheme(x0^2*y1 + x1^2*y0); # same as C1 but symmetric in the X axis
            sage: h = Hom(C3,C3)([(18*x0*y0+11*x0*y1)*el for el in [x1,x0,y1,y0]])
            sage: simpl_morphism(h)
            Scheme endomorphism of Closed subscheme of Product of projective spaces P^1 x P^1 over Rational Field defined by:
            x1^2*y0 + x0^2*y1
            Defn: Defined by sending (x0 : x1 , y0 : y1) to
                  (x1 : x0 , y1 : y0).

        However, if the original space is not the product of some spaces, the simplification can not be performed. Then we
        do the usual simplification::

            sage: h = Hom(C1,C3)([(23*x-17*y+5*z)*el for el in [x^2*z^2, z^4, y^4, z^4]]); h
            Scheme morphism:
              From: Closed subscheme of Projective Space of dimension 2 over Rational Field defined by:
              x^2 - y*z
              To:   Closed subscheme of Product of projective spaces P^1 x P^1 over Rational Field defined by:
              x1^2*y0 + x0^2*y1
              Defn: Defined on coordinates by sending (x : y : z) to
                    (23*x^3*z^2 - 17*x^2*y*z^2 + 5*x^2*z^3 : 23*x*z^4 - 17*y*z^4 + 5*z^5 , 23*x*y^4 - 17*y^5 + 5*y^4*z : 23*x*z^4 - 17*y*z^4 + 5*z^5)
            sage: simpl_morphism(h)
            Scheme morphism:
              From: Closed subscheme of Projective Space of dimension 2 over Rational Field defined by:
              x^2 - y*z
              To:   Closed subscheme of Product of projective spaces P^1 x P^1 over Rational Field defined by:
              x1^2*y0 + x0^2*y1
              Defn: Defined on coordinates by sending (x : y : z) to
                        (y : z , y^4 : z^4)
    '''
    codo_ambient = morphism.codomain().ambient_space()
    ring = morphism.domain().ambient_space().coordinate_ring()
    new_polys = morphism.defining_polynomials()
    polys = []

    ## Checking if the space is a product of projective spaces
    from sage.schemes.product_projective.space import is_ProductProjectiveSpaces as is_Product

    while(polys != new_polys):
        polys = new_polys
        if(is_Product(codo_ambient)):
            new_polys = []
            for component in codo_ambient.components():
                new_polys += __simpl_polynomials_gcd_content(polys[len(new_polys):len(new_polys)+len(component.gens())])

            new_polys = [simplify_rational_variety(ring(p), morphism.domain()) for p in new_polys]
        else:
            new_polys = [simplify_rational_variety(ring(p), morphism.domain()) for p in __simpl_polynomials_gcd_content(polys)]


    return morphism.parent()(new_polys)

def __simpl_polynomials_gcd_content(*polys):
    if(len(polys) == 1 and (type(polys) in (list, tuple))):
        polys = polys[0]

    P = parent(polys[0]); base_ring = P.base_ring()

    try:
        g = gcd(polys)
    except (TypeError, NotImplementedError): # Maybe asingular or not gcd implemented
        # we try to extract the monomials
        variables = P.gens()
        g = prod(v**min(min(mon.degree(v) for mon in poly.monomials()) for poly in polys) for v in variables)
    try:
        c= gcd([p.content() for p in polys])/g.content()
    except NotImplementedError:
        c = 1

    to_divide = g*c
    if(to_divide in base_ring): # gcd is trivial
        result = [el//to_divide for el in polys]
    else:
        result = [P(str(p//to_divide)) for p in polys]
        # v = to_divide.variables()[-1]
        # result = [P(str(p.polynomial(v)//to_divide.polynomial(v))) for p in polys]

    if(any(not el.denominator() in base_ring for el in result)):
        raise Exception("Weird error: the final results are not polynomials")
    if(any(el.denominator() != 1 for el in result)):
        ## The denominators are not the unity
        denoms = [base_ring(el.denominator()) for el in result]
        if(any(el != denoms[0] for el in denoms[1:])):
            try:
                dlcm = lcm(denoms)
                return [(el*dlcm).numerator() for el in result]
            except ArithmeticError:
                return result

    return [el.numerator() for el in result]

_CACHE_ORDER_MORPHISM = {}
@dLogFunction()
def order_morphism(morphism, bound=10):
    r'''
        Method for computing the order of a morphism up to a bound.

        Given a projective morphism `\varphi` with same domain and codomain, we can define
        its order as the minimal value of `n` such that `\varphi^n = id`. If such `n`
        does not exist, then we say `\varphi` has infinite order.

        This method checks blindly if a method has a finite order up to some power given
        by the argument ``bound``. This method also cache the answer in such a way that
        if the bound has been reached we return ``(Infinity, d, m)`` where

        * ``d`` is the current bound that have been checked.
        * ``m`` is the current value ``morphism^d``.

        Hence if the user ask for the order again with smaller bound, the answer is inmediate
        and if the user ask for the order for a higher bound only new computations are done.

        EXAMPLES::

            sage: from comb_walks.alggeo import *
            sage: P2 = ProjectiveSpace(2, QQ, 'xyz'); x,y,z = P2.gens()
            sage: C = P2.subscheme(x^2-y*z)
            sage: h = Hom(C,C)([-x,y,z]); order_morphism(h)
            2
            sage: h = Hom(C,C)([y*z, x*z, x*y]); order_morphism(h)
            2
            sage: C2 = P2.subscheme(x^3-3*x^2*y+3*x*y^2-y^3)
            sage: h = Hom(C,C2)([x,x,z]); order_morphism(h)
            +Infinity

        In the package :mod:`comb_walks.walkmodel`, we can find several examples of morphisms
        that have finite order, and also some that have infinite order::

            sage: from comb_walks.walkmodel import *
            sage: for m in AllModels: # long time (> 15 seconds)
            ....:     if(order_morphism(m.iota(1,'p')) != 2):
            ....:         print("Error in the order of x-involution on the model %s" %m.name())
            ....:     if(order_morphism(m.iota(2,'p')) != 2):
            ....:         print("Error in the order of y-involution on the model %s" %m.name())
    '''
    dlogging.log(22, "alggeo:OM: getting order (up to %d) for the morphism\n%s" %(bound,morphism))
    if(morphism.domain() != morphism.codomain()):
        return Infinity
    key = (morphism.domain(), tuple(morphism.defining_polynomials()))
    if((not key in _CACHE_ORDER_MORPHISM) or ((type(_CACHE_ORDER_MORPHISM[key]) is tuple) and (_CACHE_ORDER_MORPHISM[key][1]<bound))):
        if(key in _CACHE_ORDER_MORPHISM):
            _,current_i,current = _CACHE_ORDER_MORPHISM[key]
        else:
            current_i = 0; current = simpl_morphism(morphism)
        for i in range(current_i+1,bound+1):
            dlogging.log(22, "alggeo:OM: Cheking order %d..." %i)
            if(is_identity(current)):
                _CACHE_ORDER_MORPHISM[key] = i
                break
            current = simpl_morphism(current*morphism)
        if(not (key in _CACHE_ORDER_MORPHISM)):
            dlogging.log(22, "alggeo:OM: not found the identity. Return %s" %Infinity)
            _CACHE_ORDER_MORPHISM[key] = (Infinity,bound, current)

    return _CACHE_ORDER_MORPHISM[key]

@dLogFunction()
def is_identity(morphism):
    r'''
        Method to check if a morphism is the identity morphism or not.

        This method takes a morphism `\varphi : A \rightarrow A` and tries to
        deduce if it is the identity morphism. For doing so, first we rely
        on Sage code to check the equality and, in case it returns False,
        we try to go further:

        * For each projective component, we divide each coordinate with the
          corresponding variables. Then we check if that is the same through
          all the coordinates.

        EXAMPLES::

            sage: from comb_walks.alggeo import *
            sage: P2 = ProjectiveSpace(2, QQ, 'xyz'); x,y,z = P2.gens()
            sage: is_identity(P2.identity_morphism())
            True
            sage: is_identity(Hom(P2,P2)([x,y,z]))
            True
            sage: is_identity(Hom(P2,P2)([y,z,x]))
            False
            sage: C = P2.subscheme(x^2 - y*z); # the usual parabola
            sage: h = Hom(C,C)([x*y*z, x^2*y, x^2*z]); is_identity(h)
            True
            sage: h = Hom(C,C)([-x,-y,-z]); is_identity(h)
            True
    '''
    from sage.schemes.generic.morphism import SchemeMorphism_id
    dlogging.log(22, "alggeo:II: checking if a morphism is the identity")
    if(morphism.domain() != morphism.codomain()):
        return False
    elif(isinstance(morphism, SchemeMorphism_id)):
        return True
    space = morphism.domain(); ambient = space.ambient_space()
    polys = morphism.defining_polynomials()
    dlogging.log(22, "alggeo:II: current polynomials:\n\t- %s" %("\n\t- ".join([str(el) for el in polys])))
    vars = ambient.gens()

    ## We compute the quotiens for each projective component
    from sage.schemes.product_projective.space import is_ProductProjectiveSpaces as is_Product
    if(is_Product(ambient)):
        components = ambient.components()
    else:
        components = [ambient]

    checked = 0
    for component in components:
        quot = [polys[checked+i]/vars[checked+i] for i in range(component.ngens())]
        if(not quot[1:] == quot[:-1]): # the elements are not the same
            # We try to reduce using the variety
            quot = [simplify_rational_variety(el, space) for el in quot]
            if(not quot[1:] == quot[:-1]):
                return False
        checked += len(component.gens())

    return True

@dLogFunction()
def zeros_bihom(poly, vars, alg_name='a', diff_names=True, algebraic=__default_algebraic_extension):
    r'''
        Method to compute the zeros of a bivariate homogeneous form in the given variables.

        Let `f(x,y) \in F[x,y]` be homogeneous of degree `d`. Then:

        * `f(0,0) = 0` if and only if `d > 0`.
        * `f(ax,ay) = a^d f(x,y)`.

        Hence, if `f(x,y)` is not a constant polynomials, the zeros of a bivariate homogeneous
        polynomial are infinitely many. Here we are going to fix the zeros that we may get
        by saying that `y = 1` or `y=0` (i.e., looking solutions in the projective line).

        If `f(x,0) = 0`, then `y` divides `f(x,y)`. So, without lost of
        generality, we may assume that `f(x,0) \neq 0` and all zeros of `f(x,y)` are
        of the form `(\alpha, 1)` and all the multiples we want.

        If we evaluate `y=1` and factorized `g(x) = f(x,1)`, then we obtain several factors
        `h_1(x),\ldots,h_t(x)` where `t \leq d` (with equality when `F` is algebraically closed).
        Then the numerators of `h_i(x/y)` make a factorization of `f(x,y)` and we can describe
        all the zeros for `f(x,y)` using those minimal polynomials `h_1,\ldots,h_t`.

        If `\deg(h_j) = 1`, then we have `h_j(x,y) = ax + b`, so the point `(-b,a)` is a zero
        of the original `f(x,y)`. If the degree is higer, we may need some algebraic extension
        on the ground field in orther to express the zeros.

        For these algebraic points, we need to extend the field F using the corresponding
        polynomial `h_j(x)`. We do so using the method ``extenstion`` that can be found in any
        field when `\deg(h_j) = 2`. Otherwise we use the (possibly slower) method ``splitting_field``.

        INPUT:
            * ``poly``: a homogeneous polynomial in two variables. This is checked by the function.
            * ``vars``: the list of two variables we are going to require on the polynomial. This
              is also checked by the function.
            * ``alg_name``: name for the algebraic elements that this method generates.
            * ``diff_names``: if set to True, the algebraic elements will be named differently
              using a number after the preffix given by ``alg_name``. Since we can not guarantee
              that this method only generates one algebraic extension, it is left for the user
              to decide if they have to be distinguish or not. It is set to ``True`` by default.
            * ``algebraic``: method with interface ``(R, poly, name)`` such that takes a ring
              `R` and computes an algebraic extension using ``poly`` and ``name`` and return
              the final extension, the list of roots for ``poly`` and the number of algebraic
              extenstions required. By default, this method calls the method ``extension`` of 
              the Ring Sage class.

        OUTPUT:
            A list of tuples `(x_0,y_0)` such that ``poly(x=x0,y=y0)`` returns 0.

        EXAMPLES::

            sage: from comb_walks.alggeo import *
            sage: F.<x,y> = QQ[]
            sage: zeros_bihom(F.one(), [x, y])
            []
            sage: zeros_bihom(x-1, [x,y])
            Traceback (most recent call last):
            ...
            ValueError: Polynomial x - 1 is not homogenous or not in variables [x, y]
            sage: G.<a,b> = QQ[]
            sage: zeros_bihom(a-b, [x,y])
            Traceback (most recent call last):
            ...
            CoercionException: ...
            sage: F.<x,y,z> = QQ[]
            sage: zeros_bihom(x-z, [x,y])
            Traceback (most recent call last):
            ...
            ValueError: Polynomial x - z is not homogenous or not in variables [x, y]
            sage: zeros_bihom(x-z, [x,y,z])
            Traceback (most recent call last):
            ...
            TypeError: The requested variables ([x, y, z]) are not two --> no bivariate polynomial
            sage: zeros_bihom(y*x - y^2, [x,y])
            [(1, 0), (1, 1)]
            sage: zeros_bihom(y*x - y^2, [y,x]) # here the first coordinate is for `y`
            [(1, 1), (0, 1)]
            sage: out = zeros_bihom(x^2 + y^2, [x,y]); out
            [(a_0, 1), (-a_0, 1)]
            sage: out[0][0]^2 == -1 # checking the algebraic property for `a_0`
            True
            sage: out = zeros_bihom((x^2+y^2)*(x^2+x*y+y^2), [x,y]); out
            [(a_0, 1), (-a_0, 1), (a_1, 1), (-a_1 - 1, 1)]
            sage: (out[0][0]^2 == -1) and (out[2][0]^2 + out[2][0] + 1 == 0)
            True
    '''
    if(len(vars) != 2):
        raise TypeError("The requested variables (%s) are not two --> no bivariate polynomial" %str(vars))
    ## Casting the input ``poly`` to a common parent with the variables
    from sage.categories.pushout import pushout
    R = pushout(pushout(parent(vars[0]), parent(vars[1])), parent(poly))
    vars = [R(el) for el in vars]; poly = R(poly)

    ## Now we check the input
    if(poly.is_constant()):
        return []
    if(not poly.is_homogeneous() or any(v not in vars for v in poly.variables())):
        raise ValueError("Polynomial %s is not homogenous or not in variables %s" %(poly, vars))

    ## Creating the output variables
    result = []

    ## Treating the input
    f = poly
    x = vars[0]; y = vars[1]

    ## At this stage, we have 'f' and 'x','y' fitting the documentation notation.
    dlogging.log(22, "alggeo:zeros_bihom: computing the zeros of an homogeneous bivariate form (%s) with the variables (%s,%s)" %(f,x,y))

    ## First, we check if 'y' divides 'f'
    d = min(el.degree(y) for el in f.monomials())
    if(d > 0): # y^d divides f
        result += [(1,0)] # adding the zero
        f = R(f//y**d) # removing the factor 'y^d'
        dlogging.log(22, "alggeo:zeros_bihom: found a factor %s^%s. Adding (1,0) as zero and continuing with %s" %(y,d,f))

    ## At this point 'y' does not divide 'f'
    ## Base case: f is a constant
    if(f.degree() == 0):
        dlogging.log(22, "alggeo:zeros_bihom: the polynomial %s is constant. No zeros found" %f)
        return result

    ## Here 'f' is not divisible by 'y'. We go to a univariate polynomial for factorizing
    R2 = parent(f.polynomial(x)).change_ring(R.base()); g = R2(f(**{str(y): 1}))
    dlogging.log(22, "alggeo:zeros_bihom: evaluating %s = 1. Resulting polynomial to factor: %s" %(y,g))
    try:
        factors = g.factor() # the argument proof to avoid errors when the base field is not QQ
    except NotImplementedError:
        dlogging.log(22, "alggeo:zeros_bihom: not implemented factorization --> keeping the whole polynomial as factor (%s)" %g)
        factors = [(g,1)]
    alg = 0 # number of algebraic extensions
    for factor in factors:
        new_name = alg_name + "_%d" %alg
        fac = factor[0] # we only take the factor, not the multiplicity
        _, roots, nextensions = algebraic(R2.base(), fac, new_name)
        alg += nextensions
        result += [(root, 1) for root in roots]
        # if(fac.degree() == 0): # constant factor
        #     dlogging.log(22, "alggeo:zeros_bihom: constant factor %s in %s --> No points found" %(fac,g))
        # elif(fac.degree() == 2): # algebraic point
        #     dlogging.log(22, "alggeo:zeros_bihom: algebraic points in %s defined by %s --> Extending the field" %(g,fac))
        #     name = alg_name + ("_%d" %alg if diff_names else ""); Ra = R2.change_var(name); fac = Ra(fac)
        #     ## As the degree is 2 the two roots are easy to compute
        #     F, g = algebraic(Ra.base(), fac, name)
        #     a = fac[2]; b = fac[1]
        #     result += [(g,1), (-b-a*g, a)]
        #     alg += 1
        # elif(fac.degree() >= 3): # algebraic point
        #     dlogging.warning("alggeo:zeros_bihom: algebraic points of degree greater than 2 --> Need a splitting field\n\t- Polynomial: %s\n\t### MAY REQUIRE LONG TIME ###\n\t### Started: %s" %(fac, datetime.now().strftime("%H:%M:%S")))
        #     name = alg_name + ("_%d" %alg if diff_names else ""); Ra = R2.change_var(name); fac = Ra(fac)
        #     F = fac.splitting_field(name); fac = Ra.change_ring(F)(fac) # Now ``fac`` is on a ring where it factors
        #     dlogging.warning("alggeo:zeros_bihom: splitting field finally computed (Ended: %s)" %datetime.now().strftime("%H:%M:%S"))
        #     result += [(root[0], 1) for root in fac.roots()]
        # else:
        #     # we have a factor fac = a*x + b
        #     # we add the point (-b, a)
        #     dlogging.log(22, "alggeo:zeros_bihom: linear factor %s --> Adding point (%s, %s)" %(fac, -fac[0],fac[1]))
        #     result += [(-fac[0],fac[1])]

    ## Returning the list of points
    return result

@dLogFunction()
def point_extension(point, variety):
    r'''
        Method to create a point structure for a variety even with extensions on the field

        On Sage, algebraic subschemes are based on ground fields that are, usually, not
        algebraically closed. This means that it is very common to have points on a variety
        but Sage is unable to detect that membership property since the coordinates
        of the point are algebraic over the field over where the curve is defined.

        This method allows the user to check that membership easier doing the corresponding
        pushouts and extensions of the curve to bigger fields automatically.

        INPUT:
            * ``point``: a point. This point can be a point structure in some projective space
              or a list of coordinates. It has to be any structure such that, when we iterate
              through its elements (in the way ``for coordinate in point:...``) we obtain its
              coordinates.
            * ``variety``: algebraic scheme where we want to check the membership of ``point``.

        OUTPUT:
            The method will return the point structure for ``point`` in the corresponding exteded
            variety or an Exception if the point is not in any extension of the variety.

        EXAMPLES::

            sage: from comb_walks.alggeo import *
            sage: P1P1 = ProjectiveSpace(1, QQ, 'x').cartesian_product(ProjectiveSpace(1, QQ, 'y'))
            sage: x0,x1,y0,y1 = P1P1.gens(); O = P1P1([0,1,0,1])
            sage: C = P1P1.subscheme(x0^2*y1^2 - x0*y0*x1*y1 + x1^2*y0^2); O in C
            True
            sage: point_extension(O, C)
            (0 : 1 , 0 : 1)
            sage: F = QQ.extension(QQ[x](x^2-x+1), 'a'); a = F.gens()[0]; # created an algebraic element
            sage: point_extension([a,1,0,1], P1P1)
            (a : 1 , 0 : 1)
            sage: point_extension([a,1,1,1], C)
            (a : 1 , 1 : 1)

        It is interesting to remark that after applying this method, the Sage membership command still returns
        ``False``, but now we can recover the extended variety from the point::

            sage: point_extension([a,1,1,1], C) in C
            False
            sage: point_extension([a,1,0,1], P1P1).scheme()
            Product of projective spaces P^1 x P^1 over Number Field in a with defining polynomial x^2 - x + 1
            sage: point_extension([a,1,1,1], C).scheme()
            Closed subscheme of Product of projective spaces P^1 x P^1 over Number Field in a with defining polynomial x^2 - x + 1 defined by:
              x1^2*y0^2 - x0*x1*y0*y1 + x0^2*y1^2

        The method returns error if the point is not valid for the variety::

            sage: point_extension([1,0,a], P1P1)
            Traceback (most recent call last):
            ...
            TypeError: the list v=[1, 0, a] must have 4 components
            sage: point_extension([a,1,0,1], C)
            Traceback (most recent call last):
            ...
            TypeError: Coordinates [a, 1, 0, 1] do not define a point on ...
    '''
    from sage.categories.pushout import pushout
    FP = reduce(lambda p,q: pushout(p,q), [parent(coord) for coord in point])
    FF = pushout(variety.base_ring(), FP)
    extended_variety = variety.change_ring(FF) if FF != variety.base_ring() else variety

    return extended_variety([FF(coord) for coord in point])

@dLogFunction()
def simplify_rational_variety(func, variety):
    r'''
        Method that simplifies rational functions using the equation of a variety.

        This method takes a rational function as an input and build an equivalent rational
        function using the standard reduction performed by Sage after going to the coordinate
        ring of a variety.

        This simplification usually leads to a cannonical form inside the variety of a rational
        function and can be use to check some equalities of those rational functions that, sintactically
        seem different.

        EXAMPLES::

            sage: from comb_walks.alggeo import *
            sage: P2 = ProjectiveSpace(2, QQ, 'xyz'); x,y,z = P2.gens()
            sage: simplify_rational_variety(x^2-3*y/z, P2) == x^2 - 3*y/z
            True
            sage: C = P2.subscheme(x^2-y*z)
            sage: simplify_rational_variety(x^2-y*z, C)
            0
            sage: simplify_rational_variety(x^2/(y*z), C)
            1
            sage: simplify_rational_variety((x^3-y*x^2+3*x*z^2)/(z^3), C)
            (x*y - y^2 + 3*x*z)/z^2
    '''
    from sage.categories.pushout import pushout
    coor_ring = variety.coordinate_ring()
    if(not parent(func).is_field()): # just a polynomial
        coor_ring = pushout(parent(func), coor_ring)
        n = coor_ring(func)
        d = coor_ring.one()
    else: # a rational function
        coor_ring = pushout(parent(func.numerator()), coor_ring)
        n = coor_ring(func.numerator())
        d = coor_ring(func.denominator())

    ## Now we lift the function again to the ambient space
    from sage.rings.quotient_ring import is_QuotientRing
    if(is_QuotientRing(coor_ring)):
        n = n.lift(); d = d.lift()

    n,d = __simpl_polynomials_gcd_content(n,d)
    return n/d

@deprecation.deprecated(deprecated_in="0.1", removed_in="0.2",
    current_version="0.1",
    details="Use 'simplify_rational_variety' instead")
def simplify_on_affine_curve(func, curve_equation, trailing_var):
    '''
        Method that simplifies a rational function over a curve.

        This method reduces a rational function defined over a curve reducing the trailing_var to reduce the degree.
        It computes a canonical form where the rational function has no appearances of ``trailing_var`` of degree
        highter than ``curve_equation.degree(trailing_var)`` and it does not show up on the denominator.
    '''
    variables = curve_equation.variables()

    if((len(variables) > 2) or (not (trailing_var in variables))):
        raise ValueError("The curve is not an affine plane curve or the trailing variable is not present")
    y = trailing_var
    x = variables[1] if y==variables[0] else variables[0]
    F = curve_equation.parent().base()
    if(not F.is_field()): F = FractionField(F)
    K = func.parent()
    if(not K.is_field()): K = FractionField(K); func = K(func)

    ## At this point we have the following:
    ##  - x is the leading variable
    ##  - y is the trailing variable.
    ##  - F is the field over the curve is defined
    Fx = FractionField(PolynomialRing(F, [x])) # rational functions on 'x'
    R = PolynomialRing(Fx, [y]) # polynomial ring on 'y' over the rational functions on 'x'
    casted_curve = R(curve_equation)
    Fe = Fx.extension(casted_curve, str(y)) # algebraic extension over Fx using the equation of the curve

    ## Special case: deg_y(curve_equation) = 1 --> direct substitution
    if(casted_curve.degree() == 1):
        return K(str(func(**{str(x): Fx.gens()[0], str(y): Fe.gens()[0]})))

    ## Generic case --> usual casting
    return K(str(Fe(str(func)))) # we cast 'func' to Fe and then we convert it back.

_CACHE_APPLY_MAP = {}
@dLogFunction()
def apply_map(map, point):
    r'''
        Method to apply a map between projective varieties.

        This method applies a morphism given by ``map`` to a point ``point``. Since the morphism
        is between projective varieties, it is described by a list of polynomials. If ``point``
        is not a common zero for all those polynomials, the image is just the evaluation
        of each polynomial on the point.

        However, there are times where the point is a common zero for all the components and
        we still have an evaluation. In this method we focus on the particular case when
        the domain of ``map`` is a projective plane curve.

        See method :func:`eval_at_zero_on_variety` to know exactly how this evaluation
        is performed in each of the projective components of the image.

        INPUT:
            * ``map``: the morphism between projective varieties.
            * ``point``: a point on the domain of ``map``. This point can be given as an actual
              point on the domain or it can also be a list of coordinates.

        OUTPUT:
            A point `P` in the codomain such that ``map(point) == P`` or a ``NotImplementedError``
            in case the domain is not an algebraic curve, the curve is not smooth on the required point
            or the direct application does not work.

        EXAMPLES::

            sage: from comb_walks.alggeo import *
            sage: P2 = ProjectiveSpace(2, QQ, 'xyz'); x,y,z = P2.gens(); O = P2([0,0,1])
            sage: C = P2.subscheme(x^2 - y*z); O in C
            True
            sage: h = Hom(C,C)([z*y, z*x, x*y]); # (x, x^2) --> (1/x, 1/x^2)
            sage: h(O)
            Traceback (most recent call last):
            ...
            ValueError: [0, 0, 0] does not define a valid point since all entries are 0
            sage: apply_map(h, O)
            (0 : 1 : 0)
            sage: apply_map(h,O) in h.codomain()
            True

        This method allows also points on algebraic extensions of the ground field::

            sage: F = NumberField(QQ['a']("a^2-2"), 'a'); a = F.gens()[0]
            sage: apply_map(h, (a, 2, 1))
            (1/2*a : 1/2 : 1)
            sage: G = NumberField(QQ['i']("i^2+1"), 'i'); i = G.gens()[0]
            sage: apply_map(h, (i, 1, 1)) # point not on the curve
            Traceback (most recent call last):
            ...
            TypeError: Coordinates [i, 1, 1] do not define a point on ...
            sage: apply_map(h, (i,-1,1))
            (-i : -1 : 1)

        Also, this method can compute the image in each of the components of the product
        of Projective spaces::

            sage: C = P2.subscheme((-4)*z^3 + y^2*z + (-13/4)*x*z^2 + (-7/8)*z^3)
            sage: P1P1 = ProjectiveSpace(1, QQ, 'x').cartesian_product(ProjectiveSpace(1,QQ,'y')); x0,x1,y0,y1 = P1P1.gens()
            sage: D = P1P1.subscheme(-x0*x1*y0^2 + x0*x1*y0*y1 - x0^2*y1^2 - x0*x1*y1^2 - x1^2*y1^2)
            sage: h = Hom(C,D)([(-24)*z, 24*x + (6)*z, 12*x + 12*y + (3)*z, 24*x + (6)*z]); apply_map(h, (0,1,0))
            (0 : 1 , 1 : 0)
    '''
    key = ((map.domain(), map.codomain(), map.defining_polynomials()),point)
    dlogging.log(22, "alggeo:apply_map: applying a map to the point %s" %(str(point)))
    if(not key in _CACHE_APPLY_MAP):
        point = point_extension(point, map.domain())
        FP = point.scheme().base_ring(); map = map.change_ring(FP) if map.domain().base() != FP else map

        try:
            dlogging.log(22, "alggeo:apply_map: value not cached. Trying to apply blindly" %point)
            _CACHE_APPLY_MAP[key] = map(point)
        except: # Image not defined
            dlogging.log(22, "alggeo:apply_map: the defining polynomials can not be applied. Trying something different")

            domain = map.domain(); codomain = map.codomain(); polys = map.defining_polynomials()

            ## 1 - change coordinates so P --> origin
            change, variables = lin_change_to_zero(point)
            if(len(variables) != 2):
                raise NotImplementedError("The domain is not an affine plane curve")
            x,y = variables
            curve = domain.defining_polynomials()[0](**change)
            if(curve.derivative(x)(**{str(x): 0, str(y): 0}) == 0 and curve.derivative(y)(**{str(x): 0, str(y): 0}) == 0):
                raise NotImplementedError("The curve is not smooth in the required point")
            polys = [poly(**change) for poly in polys]

            ## 2 - get the order of each of the defining polynomials with their residues
            ambient = codomain.ambient_space()
            from sage.schemes.product_projective.space import is_ProductProjectiveSpaces as is_Product
            if(is_Product(ambient)):
                splitting = []
                total = 0
                for component in ambient.components():
                    splitting += [polys[total:total+len(component.gens())]]
                    total += len(component.gens())
            else:
                splitting = [polys]

            _CACHE_APPLY_MAP[key] = codomain(sum([eval_at_zero_on_variety(split, curve) for split in splitting], []))

    return _CACHE_APPLY_MAP[key]

@dLogFunction()
def lin_change_to_zero(point):
    r'''
        Method to get a dictionary of linear change of coordinates to the origin.

        This method takes a point in an algebraic scheme and computes a linear change of coordinates in
        its ambient space that maps ``point`` to the origin. The output is a dictionary that
        can be plugged into rational functions to get the pullback of this change of coordinates.

        **Remark**: if ``point`` is the origin, this map will lead to a simple dehomoginization.

        OUTPUT:
            * A dictionary such that ``pullback(change)(f) = f(**dict)``.
            * A list of variables equals to ``f(**dict).variables()``.

        EXAMPLES::

            sage: from comb_walks.alggeo import *
            sage: # Test for P2 and a plane curve
            sage: D = ProjectiveSpace(2, QQ, 'xyz'); x,y,z = D.gens(); O = D([0,0,1])
            sage: C = D.subscheme(x^3*z - 3*x^2*y^2 + 3*x*z^3 - z^4); O in C
            False
            sage: P = D([1,1,1]); P in C
            True
            sage: lin_change_to_zero(P)
            ({'x': x + 1, 'y': y + 1, 'z': 1}, [x, y])
            sage: O in D.subscheme([el(**lin_change_to_zero(P)[0]).homogenize(z) for el in C.defining_polynomials()])
            True
            sage: # Testing a change with an infinity point
            sage: P = D([1,0,0])
            sage: lin_change_to_zero(P)
            ({'x': 1, 'y': y, 'z': x}, [x, y])
            sage: O in D.subscheme([el(**lin_change_to_zero(P)[0]).homogenize(z) for el in C.defining_polynomials()])
            True
            sage: C = D.subscheme(x^3 - y^3 + z^3); O in C
            False
            sage: P = D([1,1,0]); P in C
            True
            sage: lin_change_to_zero(P)
            ({'x': x + 1, 'y': 1, 'z': y}, [x, y])
            sage: O in D.subscheme([el(**lin_change_to_zero(P)[0]).homogenize(z) for el in C.defining_polynomials()])
            True
            sage: # Testing with a bigger space and more complex variety
            sage: P4 = ProjectiveSpace(4, QQ, 'abcde'); a,b,c,d,e = P4.gens(); O = P4([0,0,0,0,1])
            sage: C = P4.subscheme([a^2+b^2+c^2-d^2-e^2, a^4-b^2*c^2+d*e^3]); O in C
            False
            sage: P = P4([-1,1,0,-1,1]); P in C
            True
            sage: lin_change_to_zero(P)
            ({'a': a - 1, 'b': b + 1, 'c': c, 'd': d - 1, 'e': 1}, [a, b, c, d])
            sage: O in P4.subscheme([el(**lin_change_to_zero(P)[0]).homogenize(e) for el in C.defining_polynomials()])
            True

        This method can also work with product of projective spaces::

            sage: # Testing product of two projective spaces and plane curves
            sage: P1P1 = ProjectiveSpace(1, QQ, 'x').cartesian_product(ProjectiveSpace(1, QQ, 'y'))
            sage: x0,x1,y0,y1 = P1P1.gens(); O = P1P1([0,1,0,1])
            sage: C = P1P1.subscheme(x0^2*y1^2 - x0*y0*x1*y1 + x1^2*y0^2 - x1^2*y1^2); O in C
            False
            sage: P = P1P1([1,1,1,1]); P in C
            True
            sage: lin_change_to_zero(P)
            ({'x0': x0 + 1, 'x1': 1, 'y0': y0 + 1, 'y1': 1}, [x0, y0])
            sage: O in P1P1.subscheme([el(**lin_change_to_zero(P)[0])(x0=x0/x1,y0=y0/y1).numerator() for el in C.defining_polynomials()])
            True
            sage: P = P1P1([0,1,-1,1]); P in C
            True
            sage: lin_change_to_zero(P)
            ({'x0': x0, 'x1': 1, 'y0': y0 - 1, 'y1': 1}, [x0, y0])
            sage: O in P1P1.subscheme([el(**lin_change_to_zero(P)[0])(x0=x0/x1,y0=y0/y1).numerator() for el in C.defining_polynomials()])
            True
            sage: P = P1P1([1,1,0,1]); P in C
            True
            sage: lin_change_to_zero(P)
            ({'x0': x0 + 1, 'x1': 1, 'y0': y0, 'y1': 1}, [x0, y0])
            sage: O in P1P1.subscheme([el(**lin_change_to_zero(P)[0])(x0=x0/x1,y0=y0/y1).numerator() for el in C.defining_polynomials()])
            True
            sage: # Testing with plance curves and points at infinity
            sage: P = P1P1([1,0,1,0]); # P = (inf,inf)
            sage: lin_change_to_zero(P)
            ({'x0': 1, 'x1': x0, 'y0': 1, 'y1': y0}, [x0, y0])
            sage: O in P1P1.subscheme([el(**lin_change_to_zero(P)[0])(x0=x0/x1,y0=y0/y1).numerator() for el in C.defining_polynomials()])
            True
            sage: C = P1P1.subscheme(x0^2*y0*y1 - 3*x0^2*y1^2 + x1^2*y0^2 - x1^2*y1^2); O in C
            False
            sage: P = P1P1([1,0,3,1]); P in C
            True
            sage: lin_change_to_zero(P)
            ({'x0': 1, 'x1': x0, 'y0': y0 + 3, 'y1': 1}, [x0, y0])
            sage: O in P1P1.subscheme([el(**lin_change_to_zero(P)[0])(x0=x0/x1,y0=y0/y1).numerator() for el in C.defining_polynomials()])
            True
            sage: C = P1P1.subscheme(y1^4*x1^2 - y1^2*y0^2*x0^2 + y0^4*x1*(x0 + 2*x1)); O in C
            False
            sage: P = P1P1([-2,1,1,0]); P in C
            True
            sage: lin_change_to_zero(P)
            ({'x0': x0 - 2, 'x1': 1, 'y0': 1, 'y1': y0}, [x0, y0])
            sage: O in P1P1.subscheme([el(**lin_change_to_zero(P)[0])(x0=x0/x1,y0=y0/y1).numerator() for el in C.defining_polynomials()])
            True
    '''
    ## Splitting the point into Projective components
    from sage.schemes.product_projective.space import is_ProductProjectiveSpaces as is_Product
    ambient = point.scheme().ambient_space()
    variables = ambient.gens()
    if(is_Product(ambient)):
        splitting = [point[i] for i in range(ambient.num_components())]
        splitting_vars = []
        total = 0
        for component in ambient.components():
            splitting_vars += [variables[total:total+len(component.gens())]]
            total += len(component.gens())
    else:
        splitting = [point]
        splitting_vars = [[v for v in variables]]

    result = {}; final_vars = []
    for i in range(len(splitting)):
        final_vars += splitting_vars[i][:-1] # removing the last coordinate
        split = splitting[i]
        if(split[-1] != 0): # affine point
            for j in range(len(splitting_vars[i])-1):
                result[str(splitting_vars[i][j])] = splitting_vars[i][j] + split[j]/split[-1]
            result[str(splitting_vars[i][-1])] = 1
        else: # projective part
            for m in range(len(split)-1, -1, -1):
                if(split[m] != 0):
                    k = m; break
            # we swap between that variable and the last
            result[str(splitting_vars[i][-1])] = splitting_vars[i][k]
            result[str(splitting_vars[i][k])] = 1
            for j in range(len(splitting_vars[i])-1):
                if(j != k):
                    result[str(splitting_vars[i][j])] = splitting_vars[i][j] + split[j]/split[k]
    return result, final_vars

@dLogFunction()
def lin_change_from_zero(point):
    r'''
        Method to get a dictionary of linear change of coordinates from the origin.

        This method takes a point on an algebraic scheme and computes a linear change of coordinates in
        its ambient space that maps the origin to ``point``. The output is a dictionary that
        can be plugged into rational functions to get the pullback of this change of coordinates.

        **Remark**: if ``point`` is the origin, this map will lead to a simple homoginization.

        OUTPUT:
            * A dictionary such that ``pullback(change)(f) = f(**dict).numerator()``.

        EXAMPLES::

            sage: from comb_walks.alggeo import *
            sage: # Test for P2 and a plane curve
            sage: D = ProjectiveSpace(2, QQ, 'xyz'); x,y,z = D.gens(); O = D([0,0,1])
            sage: C = D.subscheme(x^2 - y*z); # the normal parabloa
            sage: O in C
            True
            sage: P = D([1,1,1])
            sage: lin_change_from_zero(P)
            {'x': (x - z)/z, 'y': (y - z)/z, 'z': 1}
            sage: C.defining_polynomials()[0](**lin_change_from_zero(P)).numerator()
            x^2 - 2*x*z - y*z + 2*z^2
            sage: P in D.subscheme([el(**lin_change_from_zero(P)).numerator() for el in C.defining_polynomials()])
            True
            sage: # Testing a change with an infinity point
            sage: P = D([1,0,0])
            sage: lin_change_from_zero(P)
            {'x': z/x, 'y': y/x, 'z': 1}
            sage: P in D.subscheme([el(**lin_change_from_zero(P)).numerator() for el in C.defining_polynomials()])
            True
            sage: P = D([1,1,0])
            sage: lin_change_from_zero(P)
            {'x': (x - y)/y, 'y': z/y, 'z': 1}
            sage: P in D.subscheme([el(**lin_change_from_zero(P)).numerator() for el in C.defining_polynomials()])
            True
            sage: # Testing with a bigger space and more complex variety
            sage: P4 = ProjectiveSpace(4, QQ, 'abcde'); a,b,c,d,e = P4.gens(); O = P4([0,0,0,0,1])
            sage: C = P4.subscheme([a^2+b^2+c^2+d^2, a^4-b^2*c^2+d*e^3])
            sage: O in C
            True
            sage: P = P4([1,-1,0,1,1])
            sage: lin_change_from_zero(P)
            {'a': (a - e)/e, 'b': (b + e)/e, 'c': c/e, 'd': (d - e)/e, 'e': 1}
            sage: P in P4.subscheme([el(**lin_change_from_zero(P)).numerator() for el in C.defining_polynomials()])
            True

        This method can also work with product of projective spaces::

            sage: # Testing product of two projective spaces and plane curves
            sage: P1P1 = ProjectiveSpace(1, QQ, 'x').cartesian_product(ProjectiveSpace(1, QQ, 'y'))
            sage: x0,x1,y0,y1 = P1P1.gens(); O = P1P1([0,1,0,1])
            sage: C = P1P1.subscheme(x0^2*y1 - y0*x1^2); # the usual parabola
            sage: O in C
            True
            sage: P = P1P1([1,1,0,1]); # P = (1,0)
            sage: lin_change_from_zero(P)
            {'x0': (x0 - x1)/x1, 'x1': 1, 'y0': y0/y1, 'y1': 1}
            sage: P in P1P1.subscheme([el(**lin_change_from_zero(P)).numerator() for el in C.defining_polynomials()])
            True
            sage: # Testing with plance curves and points at infinity
            sage: P = P1P1([3,1,1,0]); # P = (3,inf)
            sage: lin_change_from_zero(P)
            {'x0': (x0 - 3*x1)/x1, 'x1': 1, 'y0': y1/y0, 'y1': 1}
            sage: P in P1P1.subscheme([el(**lin_change_from_zero(P)).numerator() for el in C.defining_polynomials()])
            True
            sage: P = P1P1([1,0,-2,1]); # P = (inf,-2)
            sage: lin_change_from_zero(P)
            {'x0': x1/x0, 'x1': 1, 'y0': (y0 + 2*y1)/y1, 'y1': 1}
            sage: P in P1P1.subscheme([el(**lin_change_from_zero(P)).numerator() for el in C.defining_polynomials()])
            True
            sage: P = P1P1([1,0,1,0]); # P = (inf,inf)
            sage: lin_change_from_zero(P)
            {'x0': x1/x0, 'x1': 1, 'y0': y1/y0, 'y1': 1}
            sage: P in P1P1.subscheme([el(**lin_change_from_zero(P)).numerator() for el in C.defining_polynomials()])
            True
    '''
    ## Splitting the point into Projective components
    from sage.schemes.product_projective.space import is_ProductProjectiveSpaces as is_Product
    ambient = point.scheme().ambient_space()
    variables = ambient.gens()
    if(is_Product(ambient)):
        dlogging.debug("alggeo:LCFZ: the ambient space is a product. Splitting the point and varaibles")
        splitting = [point[i] for i in range(ambient.num_components())]
        splitting_vars = []
        total = 0
        for component in ambient.components():
            splitting_vars += [variables[total:total+len(component.gens())]]
            total += len(component.gens())
    else:
        dlogging.debug("alggeo:LCFZ: the ambient space is NOT a product.")
        splitting = [point]
        splitting_vars = [[v for v in variables]]

    dlogging.debug("alggeo:LCFZ: current situation of splitting\n\t- Coordinates: %s\n\t- %s" %(splitting, splitting_vars))

    result = {}
    for i in range(len(splitting)):
        z = splitting_vars[i][-1]
        split = splitting[i]
        if(split[-1] != 0): # affine point
            for j in range(len(splitting_vars[i])-1):
                result[str(splitting_vars[i][j])] = (splitting_vars[i][j] - z*split[j]/split[-1])/z
            result[str(z)] = 1
        else: # projective part
            for m in range(len(split)-1, -1, -1):
                if(split[m] != 0):
                    k = m; break
            # we swap between that variable and the last
            x = splitting_vars[i][k]
            result[str(z)] = 1
            result[str(x)] = z/x
            for j in range(len(splitting_vars[i])-1):
                if(j != k):
                    result[str(splitting_vars[i][j])] = (splitting_vars[i][j] - x*split[j]/split[k])/x
    return result

@cached_function
def origin(variety):
    r'''
        Method to retrieve the origin of an algebraic variety.

        This method returns the origin point of the ambient space where a variety is.
        It also check if the origin belongs to that particular variety, otherwise it
        returns a ``TypeError``.

        The variety must be a subscheme of some projective space or a product of projective
        spaces. Using that information we dompute the origin for each of the components
        of the space and return it if it is on the variety.

        INPUT:
            * ``variety``: an algebraic subscheme to look for the origin

        OUTPUT:
            Either the origin point of the ambient space if it is on the variety or
            a ``TypeError``.

        EXAMPLES::

            sage: from comb_walks.alggeo import *
            sage: P1P1 = ProjectiveSpace(1, QQ, 'x').cartesian_product(ProjectiveSpace(1, QQ, 'y'))
            sage: x0, x1, y0, y1 = P1P1.gens()
            sage: origin(P1P1)
            (0 : 1 , 0 : 1)
            sage: C = P1P1.subscheme(x0^2*y1 - y0*x1^2); # usual parabola
            sage: origin(C)
            (0 : 1 , 0 : 1)

        It is important to remark that this method returns the origin **on the curve**. This means that the
        object is different although they can be checked as equals::

            sage: origin(C) is origin(P1P1)
            False
            sage: origin(C) == origin(P1P1)
            True

        This method also works with only one projective component::

            sage: P2 = ProjectiveSpace(2, QQ, 'xyz'); x,y,z = P2.gens()
            sage: origin(P2)
            (0 : 0 : 1)
            sage: C2 = P2.subscheme([x,y]); origin(C2)
            (0 : 0 : 1)
            sage: C2 = P2.subscheme(x^2 - 2*x*z + z^2 - y*z) # translated parabola
            sage: origin(C2)
            Traceback (most recent call last):
            ...
            TypeError: The origin (0 : 0 : 1) is not on ...

        And we can have even more complexes schemes::

            sage: A = ProjectiveSpace(2, QQ, 'xyz').cartesian_product(ProjectiveSpace(1, QQ, 'y')).cartesian_product(ProjectiveSpace(3, QQ, 'abcd'))
            sage: origin(A)
            ((0 : 0 : 1 , 0 : 1), (0 : 0 : 0 : 1))
    '''
    try:
        if(variety.ambient_space() is variety): # Ambient space
            from sage.schemes.product_projective.space import is_ProductProjectiveSpaces as is_Product
            if(is_Product(variety)):
                return variety(sum([[el for el in origin(component)] for component in variety.components()], []))
            else:
                n = variety.ngens()
                return variety((n-1)*[0] + [1])
        else:
            am_origin = origin(variety.ambient_space())
            if(not am_origin in variety):
                raise TypeError("The origin %s is not on %s" %(am_origin, variety))
            return variety(am_origin)
    except AttributeError: # Special case for Cartesian Producst on complicated product spaces
        from sage.sets.cartesian_product import CartesianProduct
        if(isinstance(variety, CartesianProduct)):
            return variety([origin(component) for component in variety.cartesian_factors()])
        else:
            raise TypeError("Invalid argument for this method")

def is_hypersurface(variety):
    r'''
        Method to decide wether a variety is a hypersurface or not.

        A hypersurface in affine geometry is an affine variety defined with one unique equation.
        This then can be extended to any type of projectivized space (multiple projectivations or
        standar projectivation).

        EXAMPLES::

            sage: from comb_walks.alggeo import *
            sage: P1P1 = ProjectiveSpace(1, QQ, 'x').cartesian_product(ProjectiveSpace(1, QQ, 'y'))
            sage: x0, x1, y0, y1 = P1P1.gens()
            sage: is_hypersurface(P1P1)
            False
            sage: is_hypersurface(P1P1.subscheme(x0*y1-y0*x1))
            True
            sage: is_hypersurface(P1P1.subscheme(x0^3*y1^3 + 3*x0^2*x1*y1*y0^2 + 3*x0*x1^2*y1^2*y0 + x1^3*y0^3))
            True
            sage: is_hypersurface(P1P1.subscheme([x0, y0]))
            False
            sage: P3 = ProjectiveSpace(3, QQ, 'abcd'); a,b,c,d = P3.gens()
            sage: is_hypersurface(P3)
            False
            sage: is_hypersurface(P3.subscheme(a^2*d - b^3 + c*d^2))
            True
            sage: is_hypersurface(P3.subscheme([a, a^2]))
            False
    '''
    try:
        return len(variety.defining_polynomials()) == 1
    except AttributeError: # No "defining_polynomials"
        return False

def is_prod_point(point):
    r'''
        Boolean method to check if an object is a point on a product of projective spaces

        This method checks that an element is precisely a point on an ambient space that is the
        product of several Projective Spaces.

        INPUT:
            * ``point``: the object to be checked.

        EXAMPLES::

            sage: from comb_walks.alggeo import *
            sage: P2 = ProjectiveSpace(2, QQ, 'xyz'); O = origin(P2)
            sage: is_prod_point(O)
            False
            sage: is_prod_point([0,1,1])
            False
            sage: P1P1 = ProjectiveSpace(1, QQ, 'x').cartesian_product(ProjectiveSpace(1, QQ, 'y'))
            sage: is_prod_point(origin(P1P1))
            True
    '''
    try:
        from sage.schemes.product_projective.space import is_ProductProjectiveSpaces as is_Product
        return is_Product(point.scheme().ambient_space())
    except AttributeError:
        return False

@cached_function
def is_smooth_at(variety, point):
    r'''
        Method that considers a hypersurface and check if it is smooth at a point.

        In algebraic geometry, a variety is smooth at a point if it is well approximated
        by an affine space near that point. For hypersurfaces, this property can
        be easily checked using derivatives and evaluation of the defining equation.

        Since this computation using derivatives only works for affine varieties and
        projective spaces, we will always dehomogenize around the require point (if
        it is on the curve), see method :func:`lin_change_to_zero`.

        For convention, we say that if ``point`` is not in the variety, the variety is
        **not** smooth at that point.

        EXAMPLES::

            sage: from comb_walks.alggeo import *
            sage: P2 = ProjectiveSpace(2, QQ, 'xyz'); x, y, z = P2.gens()
            sage: C = P2.subscheme(x^2-y*z); # normal parabola
            sage: O = origin(P2); P = P2([0,1,0]); Q = P2([1,0,1])
            sage: is_smooth_at(C, O)
            True
            sage: is_smooth_at(C, P)
            True
            sage: is_smooth_at(C, Q)
            False
            sage: C = P2.subscheme(x^3 - x^2*z - y^2*z)
            sage: is_smooth_at(C, O)
            False
            sage: is_smooth_at(C, P)
            True
            sage: is_smooth_at(C, Q)
            True
            sage: P1P1 = ProjectiveSpace(1, QQ, 'x').cartesian_product(ProjectiveSpace(1, QQ, 'y'))
            sage: x0,x1,y0,y1 = P1P1.gens()
            sage: C = P1P1.subscheme(x0^2*y0*y1 + y0^2*x0*x1 + x0*x1*y1^2 + y0*y1*x1^2 - x0*y0*y1*x1)
            sage: O = origin(C)
            sage: is_smooth_at(C, O)
            True
    '''
    ## Checking if the point is on the variety
    if(not point in variety):
        return False
    point = variety(point)
    change, variables = lin_change_to_zero(point)

    ## Cheking if the variety is a hypersurface
    if(not is_hypersurface(variety)):
        raise TypeError("The given variety is not a hypersurface: %s")

    poly = variety.defining_polynomials()[0](**change)
    eval_zero = {str(v) : 0 for v in variables}
    return any(poly.derivative(v)(**eval_zero) != 0 for v in variables)

def homogenize_function_on_variety(func, variety):
    r'''
        Method to homogenize a rational function using the coordinates of a variety.

        This method takes a rational function or a polynomial and computes its rational
        homogenize equivalent, i.e., a rational function where the numerator and the denominator
        are homogeneous of the same degree.

        Since there are several ways to homogenize, we use the homogenization on each projective component
        of the variety provided. If the homogeneous variable appeared on the function, and it is not
        a valid rational function, we raise an error. Otherwise we add the necessary variables.

        INPUT:
            * ``func``: the rational fucntion to homogenize
            * ``variety``: an algebraic variety used to the homogenization.

        EXAMPLES::

            sage: from comb_walks.alggeo import *
            sage: P2 = ProjectiveSpace(2, QQ, 'xyz'); x,y,z = P2.gens()
            sage: C = P2.subscheme(x^3 - 3*y*z^2 + x^2*z -z^3)
            sage: homogenize_function_on_variety(x, C)
            x/z
            sage: homogenize_function_on_variety(y, P2)
            y/z
            sage: homogenize_function_on_variety(x^2 - y, C)
            (x^2 - y*z)/z^2
            sage: homogenize_function_on_variety((x^2 - y^2)/(x*y), C)
            (x^2 - y^2)/(x*y)
            sage: homogenize_function_on_variety(x*z - y^3, P2)
            Traceback (most recent call last):
            ...
            ValueError: The homogenization variable (z) appears and the function is not a rational function

        This method also wors for producs of Projective spaces::

            sage: P1P2 = ProjectiveSpace(1, QQ, 'x').cartesian_product(ProjectiveSpace(2, QQ, 'y'))
            sage: x0, x1, y0, y1, y2 = P1P2.gens()
            sage: D = P1P2.subscheme(x0^2*y2^2 - x0*x1*y0*y1 + x1^2*y0^2)
            sage: homogenize_function_on_variety(x0 - y1, D)
            (-x1*y1 + x0*y2)/(x1*y2)
            sage: homogenize_function_on_variety(y0, P1P2)
            y0/y2
            sage: homogenize_function_on_variety(y2, D)
            Traceback (most recent call last):
            ...
            ValueError: The homogenization variable (y2) appears and the function is not a rational function
            sage: homogenize_function_on_variety(x1*y1/y2, P1P2)
            Traceback (most recent call last):
            ...
            ValueError: The homogenization variable (x1) appears and the function is not a rational function
            sage: homogenize_function_on_variety((x0 - x1)*(y0 - y1 - y2)/(x0 * y1), P1P2)
            (x0*y0 - x1*y0 - x0*y1 + x1*y1 - x0*y2 + x1*y2)/(x0*y1)
            sage: homogenize_function_on_variety(x1*y0/x0, D)
            x1*y0/(x0*y2)
    '''
    ambient = variety.ambient_space(); gens = ambient.gens()
    R = ambient.coordinate_ring(); F = FractionField(R)
    func = F(func) # casting to the field of rational functions

    from sage.schemes.product_projective.space import is_ProductProjectiveSpaces as is_Product
    if(is_Product(ambient)):
        splitting_vars = []; total = 0
        for component in ambient.components():
            n = len(component.gens())
            splitting_vars += [gens[total:total+n]]
            total += n
    else:
        splitting_vars = [gens]

    # Now we check the homogeneous condition for each set of coordinates
    for split in splitting_vars:
        num = R(func.numerator()); den = R(func.denominator())
        z = split[-1]
        if((z in num.variables()) or (z in den.variables())):
            nmons = num.monomials(); dmons = den.monomials()
            d = sum(nmons[0].degree(v) for v in split)
            if(any(sum(mon.degree(v) for v in split) != d for mon in (nmons+dmons))):
                raise ValueError("The homogenization variable (%s) appears and the function is not a rational function" %z)
        else:
            subs = {str(v) : v/z for v in split[:-1]}
            func = func(**subs)

    return F(func)


def dehomogenize_at_zero(variety):
    r'''
        Method to dehomogenize a variety defining polynomials at the origin.

        This method dehomogenize the defining polynomials of an algebraic variety
        taking into account the different types of homogenization. Since in Projective
        Spaces there are (usually) several ways to dehomogenize, we take the affine chart
        define at the origin of the ambient space.

        INPUT:
            * ``variety``: an algebraic variety. It can be either an ambient space or a subscheme.

        EXAMPLES::

            sage: from comb_walks.alggeo import *
            sage: P2 = ProjectiveSpace(2, QQ, 'xyz'); x, y, z = P2.gens()
            sage: C = P2.subscheme(x^2 - y*z); dehomogenize_at_zero(C)
            [x^2 - y]
            sage: C = P2.subscheme(x^3 - 3*z*x^2 + x*y*z - y^2*z + z^3); dehomogenize_at_zero(C)
            [x^3 - 3*x^2 + x*y - y^2 + 1]
            sage: P1P1 = ProjectiveSpace(1, QQ, 'x').cartesian_product(ProjectiveSpace(1, QQ, 'y'))
            sage: x0, x1, y0, y1 = P1P1.gens()
            sage: C = P1P1.subscheme(x0^2*y1 - x1^2*y0); dehomogenize_at_zero(C)
            [x0^2 - y0]
            sage: C = P1P1.subscheme(x0^3*y1*y0 - y0^2*x1*x0^2 + y1^2*x1^2*x0 + y1^2*x1^3); dehomogenize_at_zero(C)
            [x0^3*y0 - x0^2*y0^2 + x0 + 1]
    '''
    O = origin(variety.ambient_space())
    change, _ = lin_change_to_zero(O)
    return [poly(**change) for poly in variety.defining_polynomials()]

@dLogFunction()
def eval_at_zero_on_variety(polys, variety):
    r'''
        Method to evaluate a list of polynomials at the origin over a curve

        This method computes the projective image of a list a polynomial functions at the point the origin
        using the information that those polynomials are defined over a hypersurface ``variety``. This "projective"
        image means that not all of the values can be zero at the same time.

        First, we use the equation of the curve to reduce the polynomials and, if there is a non-zero polynomial,
        we compute the value of the list. For doing this we require that ``variety`` is a hypersurface (i.e.,
        it is defined with only one polynomial) and smooth at the origin.

        This method is closely related to the method :func:`apply_map`. This method is allowed to receive
        as input both a unique polynomial defining a curve or a hypersurface (see method :func:`order_at_variety`).
        Essentially, any input where we can decompose the algebraic object using the method :func:`decompose_at_zero`.

        INPUT:
            * ``polys``: list of polynmoials we want to evaluate at `(0,0)`.
            * ``variety``: either a hypersurface or a polynomial defining a hypersurface.

        OUTPUT:
            A list of values resulting after removing the zeros of the polynomials.

        EXAMPLES::

            sage: from comb_walks.alggeo import *
            sage: P2 = ProjectiveSpace(2, QQ, 'xyz'); x,y,z = P2.gens()
            sage: C = P2.subscheme(x^2 - y*z); # usual parabola
            sage: eval_at_zero_on_variety([x^2, y], C)
            [1, 1]
            sage: eval_at_zero_on_variety([x^2, y], x^2 - y)
            [1, 1]
            sage: C = P2.subscheme(x^3 - x^2*z - y^2*z)
            sage: eval_at_zero_on_variety([x^2-1, y^3+2-x^2], C)
            Traceback (most recent call last):
            ...
            ValueError: The curve ''x^3 - x^2 - y^2'' is singular at the point (0,0)
            sage: C = P2.subscheme(x^2 - y*z + z^2)
            sage: eval_at_zero_on_variety([x^2-1, y^3+2-x^2], C)
            Traceback (most recent call last):
            ...
            ValueError: The curve ''x^2 - y + 1'' does not go through the point (0,0)
    '''
    ## Checking if variety is a hypersurface
    if(is_hypersurface(variety)):
        dlogging.log(22, "alggeo:EZOC: computing the value of a rational function at %s\n\t- Variety: %s\n\t- Polys: %s" %(origin(variety.ambient_space()),variety, polys))
    else:
        dlogging.log(22, "alggeo:EZOC: computing the value of a rational function at origin\n\t- Curve: %s\n\t- Polys: %s" %(variety, polys))

    residues = [order_at_variety(poly, variety) for poly in polys]
    orders = [el[0] for el in residues]
    min_order = min(orders)
    return [residues[i][1] if orders[i] == min_order else 0 for i in range(len(residues))]

_CACHE_CURVE_DEC = {}
@dLogFunction()
def decompose_at_zero(curve, main_var=None):
    r'''
        Method that decomposes an affine curve at `(0,0)` in a convinient way.

        This method takes a plane curve that is smooth at `(0,0)` and then computes
        a decomposition of the form

        .. MATH::
            f(x,y) = y(b+h(x,y)) + x^dg(x),

        where the following properties hold:

        * `f(x,y)` is the curve,
        * `x` is a local parameter at `(0,0)`,
        * `y` is the other coordinate for the curve,
        * `b` is a constant,
        * `h(x,y)` is a polynomial with `h(0,0) = 0`,
        * `g(x)` is a polynomial with `g(0)=0`.

        This indicates that `x` has a zero of order 1 at `(0,0)` and `y` has a zero of order `d`.
        This can easily help to compute the order of rational functions over the curve at `(0,0)`.

        This method cache the result, although different calls with different ``main_var`` arguments
        will lead to repeat computations sice we may have that the other variable is NOT a local
        parameter.

        INPUT:
            * ``curve``: a projective hypersurface or the defining polynomial in two variables of the curve.
            * ``main_var``: optional argument to indicate which of the variables is
              better for considering as a local parameter on the curve.

        OUTPUT:
            The output of this method is the tuple `(d,g,b,h,X,Y)` where `d`, `g`, `b`, `h`
            are the described elements before, `X` is the local parameter chosen and `Y` the remaining
            variable.

        EXAMPLES::

            sage: from comb_walks.alggeo import *
            sage: R.<x,y> = QQ[]
            sage: f = x^4 + 2*y^2*x^2 - y; decompose_at_zero(f)
            (4, 1, -1, 2*x^2*y, x, y)
            sage: R.<x,y,z> = QQ[]
            sage: f = x^3 - 3*x^2*y + 3*x*y^2 - y^3 + x; decompose_at_zero(f)
            (3, -1, 1, x^2 - 3*x*y + 3*y^2, y, x)
            sage: R.<x,y,z> = QQ.extension(QQ['i']("i^2+1"), 'i')[]; i = R.base().gens()[0]
            sage: f = i*z^3 - 2*(i-1)*x^2*z + x - z; decompose_at_zero(f)
            (1, 1, -1, (-2*i + 2)*x^2 + (i)*z^2, x, z)
            sage: f = z + x + y; decompose_at_zero(f)
            Traceback (most recent call last):
            ...
            TypeError: The curve ''x + y + z'' is defined with an innapropriate number of variables (Expected 2, got 3)
            sage: f = x^3 - x^2 - 3*y^2; decompose_at_zero(f)
            Traceback (most recent call last):
            ...
            ValueError: The curve ''x^3 - x^2 - 3*y^2'' is singular at the point (0,0)
            sage: f = x^2 - 2*y + 1; decompose_at_zero(f)
            Traceback (most recent call last):
            ...
            ValueError: The curve ''x^2 - 2*y + 1'' does not go through the point (0,0)
            sage: f = 3*y^3 + 2*x*y^2 + y; decompose_at_zero(f)
            (+Infinity, 0, 1, 2*x*y + 3*y^2, x, y)


        We can use the argument ``main_var`` to try to use that variable as a local parameter. Only if both
        variables are local parameters the result will be different::

            sage: f = x^3 - y; decompose_at_zero(f, x)
            (3, 1, -1, 0, x, y)
            sage: decompose_at_zero(f, y)
            (3, 1, -1, 0, x, y)
            sage: f = x^3 - x - y; decompose_at_zero(f, x)
            (1, x^2 - 1, -1, 0, x, y)
            sage: decompose_at_zero(f, y)
            (1, -1, -1, x^2, y, x)

        This method can also be applied to projective varieties that defines plane curves::

            sage: P1P1 = ProjectiveSpace(QQ, 1, 'x').cartesian_product(ProjectiveSpace(QQ, 1, 'y'))
            sage: x0,x1,y0,y1 = P1P1.gens()
            sage: C = P1P1.subscheme(x0^2*y1 - x1^2*y0); # the usual parabola
            sage: decompose_at_zero(C, x0)
            (2, 1, -1, 0, x0, y0)
            sage: P2 = ProjectiveSpace(QQ, 2, 'xyz'); x, y, z = P2.gens()
            sage: C = P2.subscheme(x^3 - 2*y^2*z + x*z^2)
            sage: decompose_at_zero(C)
            (2, -2, 1, x^2, y, x)
    '''
    if(is_hypersurface(curve)):
        curve = dehomogenize_at_zero(curve)[0]

    ## Checking the input
    variables = list(curve.variables())
    if(len(variables) != 2):
        raise TypeError("The curve ''%s'' is defined with an innapropriate number of variables (Expected 2, got %d)" %(curve, len(variables)))
    if(main_var != None and main_var in variables):
        x = variables.pop(variables.index(main_var)); y = variables[0]
    else:
        x = variables[0]; y = variables[1]
    ox = x
    ## Checking the cached variable
    if(not ((curve,ox) in _CACHE_CURVE_DEC)):
        eval_zero = {str(x): 0, str(y): 0}

        if(curve(**eval_zero) != 0):
            raise ValueError("The curve ''%s'' does not go through the point (0,0)" %curve)

        a = curve.derivative(x)(**eval_zero); b = curve.derivative(y)(**eval_zero)
        if(a == 0 and b == 0):
            raise ValueError("The curve ''%s'' is singular at the point (0,0)" %curve)

        ## Deciding the local parameter
        if(b == 0): # x is not a local parameter --> y is local parameter
            dlogging.log(22, "alggeo:DCAT: swapping variables (%s is not a local parameter)" %x)
            aux = x; x = y; y = aux
            aux = a; a = b; b = aux

        ## At this point we have the following
        ## 'x' is the local parameter
        ## 'y' is the other variable
        curve_y0 = curve(**{str(y):0})
        mult = lambda p, q : p*q
        if(curve_y0 == 0): # case ord(y) = +Infinity
            d = Infinity; g = 0
        else:
            d = min(el.degree(x) for el in curve_y0.monomials())
            ## Computing the divisions --> going monomial to monomial to avoid division problems
            g = parent(curve)(sum(map(mult, [mon//x**d for mon in curve_y0.monomials()], curve_y0.coefficients())))
        curve_y_nob = curve - curve_y0 - y*b
        h = parent(curve)(sum(map(mult, [mon//y for mon in curve_y_nob.monomials()], curve_y_nob.coefficients())))

        _CACHE_CURVE_DEC[(curve,ox)] = (d,g,b,h,x,y)
        dlogging.log(22, "alggeo:DCAT: curve decomposed\n\t- local parameter: %s\n\t- b: %s\n\t- h: %s\n\t- d: %s\n\t- g: %s" %(x, b,h,d,g))

    return _CACHE_CURVE_DEC[(curve,ox)]

@dLogFunction()
def __order_poly_at_variety(poly, variety, main_var=None):
    r'''
        Method to compute the order and the residue of a polynomial at the origin on an algebraic variety.

        This method computes the order of a polynomial function over a curve at the origin. If ``variety``
        defines an affine curve that is regular at `(0,0)`, then there is a local parameter `t`. Then,
        any rational function can be written like

        .. MATH::
            F(t) = \sum_{k \geq m} f_k t^k,

        where `f_m \neq 0`. We say that `m` is the order of `F` and `f_m` is its residue.

        Any polynomial function has a non-negative order, and we define that the order of the
        zero function is `\infty` with residue `0`.

        INPUT:
            * ``poly``: the polynomial function
            * ``variety``: a hypersurface or a deffining polynomial for an affine curve regular at `(0,0)`.
            * ``main_var``: variable that will be considered *local parameter* if possible.

        OUTPUT:
            A triplet containing:

            * An integer with the order of ``poly`` at `(0,0)` over ``variety``,
            * An element representing the residue (the first non-zero coefficient) of ``poly``,
            * The affine local parameter used for computing the residue.
    '''
    if(is_hypersurface(variety)):
        dlogging.log(22, "alggeo:OPAC: getting order at %s for the polynomial %s over the variety %s" %(origin(variety.ambient_space()),poly, variety))
        variety = dehomogenize_at_zero(variety)[0]
    else:
        dlogging.log(22, "alggeo:GOPAC: getting order at (0,0) for the polynomial %s over the curve %s" %(poly, variety))

    d,g,b,h,x,y = decompose_at_zero(variety, main_var)
    if(d == Infinity): # extreme case y=0 --> the order is just the minimal degree on x.
        poly = poly(**{str(y):0})
        if(poly == 0):
            return (Infinity, 0, x)
        else:
            order = min(mon.degree(x) for mon in poly.monomials()); poly = poly//x**order
            return (order, poly(**{str(x):0}), x)

    # Checking the variables of the polynomials
    if(any(not el in (x,y) for el in poly.variables())):
        raise TypeError("The variables between the curve and the polynomial do not match")

    ## Starting the main decomposition
    eval_zero = {str(x) : 0, str(y) : 0}
    R = variety.parent(); F = FractionField(R)
    quotR = R.quotient(variety)
    current = poly
    den = 1
    order = 0
    while(current(**eval_zero) == 0):
        # Checking the polynomials is not the zero
        if(quotR(current) == 0):
            dlogging.log(22, "alggeo:GOPAC: the polynomial is zero")
            return (Infinity, 0, x)

        dlogging.log(22, "alggeo:GOPAC: evaluation still 0. Current polynomial %s" %current)
        current_order = min(mon.degree(x) + d*mon.degree(y) for mon in current.monomials())
        dlogging.log(22, "alggeo:GOPAC: detected order %d for local parameter." %current_order)
        ## for evaluating the polynomial we divide monomial by monomial to avoid errors in division
        evaluation = F(current(**{str(y) : (-x**d*g)/(b+h)}))
        num = evaluation.numerator()
        current = R(sum(map(lambda p,q : p*q, [mon//x**current_order for mon in num.monomials()], num.coefficients())))
        den *= evaluation.denominator()(**eval_zero)
        order += current_order

    result = (order, current(**eval_zero)/den, x)
    dlogging.log(22, "alggeo:GOPAC: final order %s. Residue: %s" %(result[0],result[1]))
    return result

@dLogFunction()
def order_at_variety(rational, variety, main_var=None):
    r'''
        Method to compute the order and the residue of a rational function at `(0,0)` over an affine curve.

        This method computes the order of a polynomial function over a curve at `(0,0)`. If ``curve``
        defines an affine curve that is regular at `(0,0)`, then there is a local parameter `t`. Then,
        any rational function can be written like

        .. MATH::
            F(t) = \sum_{k \geq m} f_k t^k,

        where `f_m \neq 0`. We say that `m` is the order of `F` and `f_m` is its residue.

        We define that the order of the zero function is `\infty` with residue `0`.

        INPUT:
            * ``rational``: the polynomial function
            * ``variety``: a hypersurface smooth at the origin or a polynomial defining an affine curve smooth at (0,0).
            * ``main_var``: variable that will be considered *local parameter* if possible.

        OUTPUT:
            A triplet containing:

            * An integer with the order of ``rational`` at the origin over ``variety``,
            * An element representing the residue (the first non-zero coefficient) of ``poly``,
            * The affine local parameter used for computing the residue.

        EXAMPLES::

            sage: from comb_walks.alggeo import *
            sage: P2 = ProjectiveSpace(QQ, 2, 'xyz'); x,y,z = P2.gens()
            sage: C = P2.subscheme(x^3 - 3*x*y*z + 7*y^2*z - y*z^2)
            sage: order_at_variety(x, C)
            (1, 1, x)
            sage: order_at_variety(y, C)
            (3, 1, x)
            sage: order_at_variety(7*y^2*x+ 9*y^3, C)
            (7, 7, x)
            sage: order_at_variety((3*x^7+2*y^2)/(3*x^6 + y^4), C)
            (0, 2/3, x)
            sage: order_at_variety(0, C)
            (+Infinity, 0, x)

        This method can also work with a defining polynomial in two variables instead of the projective variety::

            sage: P1P1 = ProjectiveSpace(QQ, 1, 'x').cartesian_product(ProjectiveSpace(QQ, 1, 'y'))
            sage: x0, x1, y0, y1 = P1P1.gens()
            sage: C = P1P1.subscheme(x0^3*y1^2 - 3*x0*x1^2*y0*y1 + 7*y0^2*x1^3 - y0*y1*x1^3)
            sage: order_at_variety(x0, C) == order_at_variety(x0, dehomogenize_at_zero(C)[0])
            True
            sage: order_at_variety(y0, C) == order_at_variety(y0, dehomogenize_at_zero(C)[0])
            True
            sage: order_at_variety((3*x0+y0^2)/x0^6, C) == order_at_variety((3*x0+y0^2)/x0^6, dehomogenize_at_zero(C)[0])
            True
    '''
    ## Checking if variety is a hypersurface
    if(is_hypersurface(variety)):
        dlogging.log(22, "alggeo:ORAC: getting order at %s for the function %s on the variety %s" %(origin(variety.ambient_space()),rational,variety))
        R = variety.ambient_space().coordinate_ring()
    else:
        dlogging.log(22, "alggeo:ORAC: getting order at (0,0) for the function %s" %rational)
        R = parent(variety)
        if(R.is_field()): R = R.base() # going to a polynomial ring
    F = FractionField(R)
    rational = F(rational)

    num = R(rational.numerator()); den = R(rational.denominator())
    on, rn, x = __order_poly_at_variety(num, variety, main_var)
    od, rd, x = __order_poly_at_variety(den, variety, main_var)

    if(od == Infinity):
        raise ValueError("The denominator %s is not defined on the curve %s" %(den, variety))
    elif(on == Infinity): # Case the rational function is always zero.
        return (Infinity, 0, x)

    return (on-od, rn/rd, x)

_CACHE_ASYMPTOTICS = {}
@dLogFunction()
def asymptotics(variety, func, point):
    r'''
        Method to compute a asymptotic approximation of a rational function.

        This methods allows the user to compute asymptotic information around one point
        on a variety. This variety must be a plane curve or the code woult not work properly.

        This method will check that the given point (which can be defined in an algebraic
        extension field) is on the curve and then compute the local expansion of the rational
        function given by ``func`` around that point.

        This method is equivalent to :func:`order_at_variety` when the point is the
        origin. This is an enhanced method that allows more flexibility on the point and take care
        of the changes of coordinates required to compute this asymptotic data.

        INPUT:
            * ``variety``: a hypersurface that defines a plane affine curve after its dehomogenization.
            * ``func``: a rational function on the variety. This method will check out that it is a valid
              rational function. This means either it is an affine rational function in the usual sense, or
              both numerator and denominator need to be homogeneous of the same degree.
            * ``point``: a point on the variety. It can have coordinates in extensions of the base ring
              of the variety.

        OUTPUT:
            A triplet containing:

            * The order of the function ``func`` at ``point`` on the variety.
            * The first non-zero coefficient of the expansion of ``func`` around ``point``.
            * The local parameter on ``variety`` used to compute the expansion of ``func`` around ``point``.

        EXAMPLES::

            sage: from comb_walks.alggeo import *
            sage: P2 = ProjectiveSpace(2, QQ, 'xyz'); x,y,z = P2.gens()
            sage: C = P2.subscheme(x^2 - y*z); # the usual parabola
            sage: O = origin(C); P = C([0,1,0]); # origin and the point at infinity
            sage: asymptotics(C, x, O)
            (1, 1, x/z)
            sage: asymptotics(C, y, O)
            (2, 1, x/z)
            sage: asymptotics(C, x/z, O) == asymptotics(C, x, O)
            True
            sage: asymptotics(C, x/z, P)
            (-1, 1, x/y)
            sage: asymptotics(C, y/z, P)
            (-2, 1, x/y)
            sage: asymptotics(C, y/z - (y/x)^2, P)
            (+Infinity, 0, x/y)
            sage: asymptotics(C, (x^2 - 3*y^2)/(7*x^3), P)
            (-1, -3/7, x/y)
            sage: asymptotics(C, (x^2 - 3*y^2)/(7*x^3) + (3/7)*(y/x), P)
            (1, 1/7, x/y)

        This method also allows to study the asymptotics around algebraic points::

            sage: F = QQ.extension(QQ[x](x^2 + 1), 'i'); i = F.gens()[0]
            sage: Q = point_extension([i, -1, 1], C)
            sage: asymptotics(C, x^2+1, Q)
            (1, (2*i), (x + (-i)*z)/z)
            sage: asymptotics(C, (y^2-1)/(x^2+1), Q)
            (0, -2, (x + (-i)*z)/z)
    '''
    point = point_extension(point, variety); FP = point.scheme().base_ring()
    variety = variety.change_ring(FP) if FP != variety.base_ring() else variety
    func = homogenize_function_on_variety(func, variety)

    key = (variety,func.numerator(),func.denominator(), point)
    if(not key in _CACHE_ASYMPTOTICS):
        if(not is_hypersurface(variety)):
            raise TypeError("Asymptotics only implemented for Hypersurfaces")
        equation = variety.defining_polynomials()[0]

        ## Move the point to the origin
        change, _ = lin_change_to_zero(point)
        ## Applying the change of coordinates
        nequation = equation(**change); nfunc = func(**change)

        ## Compute the local expansion of ``nfunc`` at the origin
        order, res, loc = order_at_variety(nfunc, nequation)

        ## We transform the local parameter
        bchange = lin_change_from_zero(point)
        _CACHE_ASYMPTOTICS[key] = (order, res, loc(**bchange))
    return _CACHE_ASYMPTOTICS[key]

_CACHE_POLAR_PART = {}
@dLogFunction()
def polar_part(variety, func, point, sequence=False):
    r'''
        Method that gets the polar part at one point of a rational function.

        Given a projective variety `A` and a point `P \in A` where the variety
        is smooth, we can have a *local parameter* `t \in C(A)`, i.e., a function
        that vanishes at `P` with *order* 1. This local parameter generates the ideal
        of all rational functions over `A` that vanish at `P`.

        In fact, given a rational function `f \in C(A)`, we can compute a local expansion
        of `f` around `P` using this local parameter such that:

        .. MATH::

            f = \sum_{k\geq d} f_d t^d,

        where `d` is defined as the order of `f` at `P`. If `d < 0` we say that `f` has a pole
        at `P`. And we say that the part of the expansions with negative exponents of `t` is
        the *polar part of `f` at `P` w.r.t. `t`*.

        Since any two local parameters differs by a constant, then the polar part of `f` is almost
        uniquely defined. If we consider the polar part as the list of coefficients `[0,f_{-1}, f_{-2},\ldots]`,
        then this list is uniquely determined up to a multiplication termwise by the geometric sequence
        `[1,c, c^2, \ldots]`.

        INPUT:
            * ``variety``: variety over we are considering the function.
            * ``func``: rational function over ``variety``.
            * ``point``: a point on the variety. It can be a point defined over an algebraic extenstion of the
              ground field of ``variety``.
            * ``sequence``: boolean value to determine if we return the whole polar part function or the sequence
              of the Laurent expansion with respect to the local parameter. In the last case, the output will be
              a list of values ``l`` where ``l[i]`` represents the value `f_{-i}`.

        OUTPUT:
            A tuple containing the polar part and the local parameter we used to compute it.

        EXAMPLES::

            sage: from comb_walks.alggeo import *
            sage: P2 = ProjectiveSpace(2, QQ, 'xyz'); x,y,z = P2.gens()
            sage: C = P2.subscheme(x^3 - 3*y^2*z + x^2*z + y*z^2); O = origin(C)
            sage: polar_part(C, 1/x^3 - x/y, O)
            ((x^2*z + z^3)/x^3, x/z)
            sage: polar_part(C, 1/x^3 - x/y, O, True)
            ([0, 1, 0, 1], x/z)
            sage: C = P2.subscheme(x^3 - y^2*z + 7*x*z^2 + 3*z^3); P = C([0,1,0]);# elliptic curve
            sage: polar_part(C, y, P, True)
            ([0, 0, 0, 1], x/y)
            sage: polar_part(C, y, P)
            (y^3/x^3, x/y)
            sage: polar_part(C, x^3 - y^2 + 3*x*y, P)
            ((-42*x^4*y - 7*x^3*y^2 + 3*y^5)/x^5, x/y)
            sage: polar_part(C, x^3 - y^2 + 3*x*y, P, True)
            ([0, -42, -7, 0, 0, 3], x/y)
    '''
    point = point_extension(point, variety); FP = point.scheme().base_ring()
    variety = variety.change_ring(FP) if FP != variety.base_ring() else variety
    func = homogenize_function_on_variety(func, variety)

    key = (variety, func.numerator(), func.denominator(), point, sequence)
    if(not key in _CACHE_POLAR_PART):

        polar_part = 0
        seq = {}
        current_order, current_residue, local_par = asymptotics(variety, func, point)
        while(current_order < 0):
            dlogging.log(22, "alggeo:PP: still a pole.\n\t- Polar part: %s\n\t- Current order: %d" %(polar_part, current_order))
            seq[-current_order] = current_residue
            polar_part += current_residue*(local_par**current_order)
            current_order, current_residue, local_par = asymptotics(variety, func - polar_part, point)

        if(sequence):
            _CACHE_POLAR_PART[key] = ([seq.get(i, 0) for i in range(max(seq.keys()) + 1)], local_par)
        else:
            _CACHE_POLAR_PART[key] = (polar_part, local_par)
    return _CACHE_POLAR_PART[key]

def expand_at_point(variety, func, point, bound):
    r'''
        Method to expand a rational function on a variety using a local parameter.

        Given a projective variety `A` and a point `P \in A` where the variety
        is smooth, we can have a *local parameter* `t \in C(A)`, i.e., a function
        that vanishes at `P` with *order* 1. This local parameter generates the ideal
        of all rational functions over `A` that vanish at `P`.

        In fact, given a rational function `f \in C(A)`, we can compute a local expansion
        of `f` around `P` using this local parameter such that:

        .. MATH::

            f = \sum_{k\geq d} f_d t^d,

        where `d` is defined as the order of `f` at `P`.

        This method computes a local parameter `t` for the variety given by ``variety``
        and the corresponding sequence of elements `f_k` for `d \leq k < bound`.

        INPUT:
            * ``variety``: the variety `A` to perform the computations,
            * ``func``: the rational function over `A`. It can be given a an affine rational
              function (and we homogenize it) or as a projective rational function (i.e., a
              rational function defined as a quotient of two homogeneous polynomials of same
              degree).
            * ``point``: a point `P` on the variety `A`.
            * ``bound``: and integer number.

        OUTPUT:
            A tuple ``(d,t)`` such that ``d[n]`` returns the coefficient `f_n` in the expansion
            with respect to ``t`` of ``func`` around ``point`` in ``variety``.

        EXAMPLES::

            sage: from comb_walks.alggeo import *
            sage: P2 = ProjectiveSpace(2, QQ, 'xyz'); x,y,z = P2.gens()
            sage: C = P2.subscheme(x^3 - 3*y^2*z + x^2*z + y*z^2); O = origin(C)
            sage: expand_at_point(C,1/x^3, O, 10)
            ({-3: 1,
              -2: 0,
              -1: 0,
              0: 0,
              1: 0,
              2: 0,
              3: 0,
              4: 0,
              5: 0,
              6: 0,
              7: 0,
              8: 0,
              9: 0},
             x/z)
            sage: expand_at_point(C,x/y, O, 5)
            ({-1: -1, 0: 1, 1: -4, 2: 1, 3: 8, 4: 10}, x/z)
            sage: all(expand_at_point(C,1/x^3 - x/y, O,10)[0].get(i,0) == expand_at_point(C,1/x^3, O,10)[0].get(i,0) - expand_at_point(C,x/y, O,10)[0].get(i,0) for i in range(-3,9))
            True

        TODO:
            Add examples and tests

    '''
    point = point_extension(point, variety); FP = point.scheme().base_ring()
    variety = variety.change_ring(FP) if FP != variety.base_ring() else variety
    func = homogenize_function_on_variety(func, variety)

    res = {}
    current_order, current_residue, local_par = asymptotics(variety, func, point)
    original_order = current_order
    removed = 0
    while(current_order < bound):
        res[current_order] = current_residue
        removed += current_residue*(local_par**current_order)
        current_order, current_residue, local_par = asymptotics(variety, func - removed, point)

    ## Adding the zero coefficients
    if(len(res) > 0):
        for i in range(original_order, bound):
            if(not (i in res)):
                res[i] = 0

    return (res, local_par)
