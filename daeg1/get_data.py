r'''
    File containing the methods used to compute, create and visualize data

    In this file we offer the methods required to create HTML or LaTeX tables with the
    desired data from the models for Walks in the quarter plane defined in the file
    :mod:`daeg1.walkmodel`.

    AUTHORS:
        - Antonio Jimenez-Pastor (2020-03-19): initial version
        
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

from sage.all import (latex, var, Infinity)

from .alggeo import (is_prod_point, order_morphism, asymptotics, pullback)
from .walkmodel import (FiniteGroup, NonEllipticC, EllipticC, AllModels,
    ModelDict, WalkModel, x0,x1,y0,y1)

from logging import ERROR
from . import dlogging
from .dlogging import dLogFunction

### Limiting time context manager
import signal
from contextlib import contextmanager

class TimeoutException(KeyboardInterrupt): pass

@contextmanager
def time_limit(seconds):
    def signal_handler(signum, frame):
        dlogging.warning("time_limit: exceeded maximum time of %s" %seconds)
        raise TimeoutException()
    signal.signal(signal.SIGALRM, signal_handler)
    signal.alarm(seconds)
    try:
        yield
    finally:
        signal.alarm(0)


### Methods to store data
def apply_method(method, avoid_fg = False, avoid_ne = False, avoid_ie = False, verbose=True):
    r'''
        Method to gather the data from a method to the selected type of models.

        INPUT:
            * ``method``: a function that takes a WalkModel and returns a list of data.
            * ``avoid_fg``: set to ``True`` if the user wants to avoid the computation on the models
              with Finite Group.
            * ``avoid_ne``: set to ``True`` if the user wants to avoid the computation on the models
              with non-elliptic kernel curves.
            * ``avoid_ie``: set to ``True`` if the user wants to avoid the computation on the models
              with Infinite Group and elliptic kernel curve.
            * ``verbose``: set to ``False`` if the user wants to avoid the printing of the progress bar.
    '''
    from sage.misc.misc import get_verbose, set_verbose
    prev_verbose = get_verbose(); set_verbose(-1)

    dict_of_results = [{},{},{}]
    total = 0
    if(not avoid_fg): total += len(FiniteGroup)
    if(not avoid_ne): total += len(NonEllipticC)
    if(not avoid_ie): total += len(EllipticC)
    iteration = 0
    try:
        if(verbose): print_progress_bar(iteration, total)
        if(not avoid_fg):
            ## First we apply to models with Finite group
            for m in FiniteGroup:
                if(verbose): print_progress_bar(iteration, total, suffix=m.name())
                try:
                    dict_of_results[0][m.name()] = method(m)
                except Exception as e:
                    dict_of_results[0][m.name()] = e

                iteration += 1
                if(verbose): print_progress_bar(iteration, total, suffix=m.name())
        if(not avoid_ne):
            ## Then we apply to models with NonElliptic curve
            for m in NonEllipticC:
                if(verbose): print_progress_bar(iteration, total, suffix=m.name())
                try:
                    dict_of_results[1][m.name()] = method(m)
                except Exception as e:
                    dict_of_results[1][m.name()] = e

                iteration += 1
                if(verbose): print_progress_bar(iteration, total, suffix=m.name())
        if(not avoid_ie):
            ## Finally we apply to models with Infinite Group and Elliptic curve
            for m in EllipticC:
                if(verbose): print_progress_bar(iteration, total, suffix=m.name())
                try:
                    dict_of_results[2][m.name()] = method(m)
                except Exception as e:
                    dict_of_results[2][m.name()] = e

                iteration += 1
                if(verbose): print_progress_bar(iteration, total, suffix=m.name())
        if(verbose): print("")
    except KeyboardInterrupt:
        if(verbose): print("")
        pass

    set_verbose(prev_verbose)
    return dict_of_results

def mlatex(element,open="$",close="$"):
    r'''
        Generic method to format Sage objects to LaTeX.

        This method allows to have different treatment for python ans Sage objects
        different than the method ``latex``. It also allows to use different opening
        and closing characters for the expressions, so it is useful for MathJax and
        LaTeX.

        The distinguished objects so far are:
            * ``str``: strings are interpreted as LaTeX code directly.
            * Points on the product of Projective spaces: we do the nice printing of these type of points.
            * Lists: are printed as a tuple with square brackets.
            * Tuple: are printed as a tuple with round brackets.
            * Dictionaries: are printed as a map: "key -> value" i a column format.

        Any other elements is printed using the method ``latex``.
    '''
    if(type(element) == str):
        return open + element + close
    elif(is_prod_point(element)): # special case for double projective points
        res = open + "\\left("
        res += ", ".join(["\\infty" if element[i][1] == 0 else mlatex(element[i][0], "", "") for i in range(element.scheme().ambient_space().num_components())])
        res += "\\right)" + close
        return res
    elif(type(element) == list):
        #return open + "\\left[\\begin{array}{c}" + "\\\\".join([mlatex(part,"", "") for part in element]) + "\\end{array}\\right]" + close
        return open + "\\left[" + " , ".join([mlatex(part, "","") for part in element]) + "\\right]" + close
    if(type(element) == tuple):
        #return open + "\\left(\\begin{array}{c}" + "\\\\".join([mlatex(part, "", "") for part in element]) + "\\end{array}\\right)" + close
        return open + "\\left(" + " , ".join([mlatex(part, "","") for part in element]) + "\\right)" + close
    elif(type(element) == dict):
        return open + "\\begin{array}{ccc}" + "\\\\".join(["%s & \\rightarrow & %s" %(mlatex(k, "", ""),mlatex(v, "", "")) for (k,v) in element.items()]) + "\\end{array}" + close
    return open + latex(element) + close

def make_latex_table(columns, rows, types=None):
    r'''
        Method to create a LaTeX table.

        This method takes the data and create the LaTeX code necessary to visualize it on a table.
        The user needs to provide the name of the data columns and each of the rows of data.

        Each *row* has to have the following format:
            * The first element has to be the name of the model. It will be used as the first column, before the
              data begins.
            * The second element has to be either an element (i.e., an error ocurred for this data) or a list of
              the exact length of the columns we have.

        The user can use the argument ``types`` to declare how to align the elements on the table.
    '''
    if(types == None):
        n_type = len(columns)*["c"]
    else:
        n_type = types
    res = "\\begin{longtable}{|" + "|".join(["c"]+n_type) + "|}\n\\hline\n"
    ## Creating the title row
    res += " & ".join([""] + ["\\textbf{%s}" %el for el in columns]) + "\\\\\\hline\\hline\n"
    ## Create data for each row
    for row in rows:
        if((type(row[1]) in (list, tuple)) and (len(row[1]) == len(columns))):
            res += ("\t %s & " %row[0])
            res += " & ".join([mlatex(el) for el in row[1]]) + "\\\\\\hline\n"
        else:
            res += ("\t %s & " %row[0]) + "\\multicolumn{%d}{l|}{%s}\\\\\\hline\n" %(len(columns), str(row[1]).replace("''", "$").replace("'", "$").replace("*", ""))
    ## Closing the table
    res += "\\end{longtable}\n"
    return res

def make_html_table(columns, rows, types=None):
    r'''
        Method to create an HTML table.

        This method takes the data and create the HTML code necessary to visualize it on a table.
        The user needs to provide the name of the data columns and each of the rows of data.

        Each *row* has to have the following format:
            * The first element has to be the name of the model. It will be used as the first column, before the
              data begins.
            * The second element has to be either an element (i.e., an error ocurred for this data) or a list of
              the exact length of the columns we have.

        The user can use the argument ``types`` to declare how to align the elements on the table.

        **WARNING**: currently the argument ``types`` is useless.
    '''
    ## First, we create the switches
    res = "<div id='column_switchers'>\n"
    i = 1
    for column in columns:
        res += "\t<p>\n"
        res += "\t\t<label class='switch'>\n"
        res += "\t\t\t<input type='checkbox' onclick='document.getElementById(\"input_table\").classList.toggle(\"hide%d\")' checked>\n" %(i+1)
        res += "\t\t\t<span class='slider round'></span>\n"
        res += "\t\t</label>\n"
        res += "\t\t%s\n" %column
        res += "\t<p>"
        i += 1
    res += "</div>\n"

    ## Second, we create the table
    res += "<table id=\"input_table\">\n"
    ## Header line
    res += "\t<tr>\n\t\t<th onclick=\"w3.sortHTML('#input_table', '.row', 'td:nth-child(1)')\" style=\"cursor:pointer\">Name of the model</th>\n" # starting row and column for names
    i = 2
    for column in columns:
        res += "\t\t<th onclick=\"w3.sortHTML('#input_table', '.row', 'td:nth-child(%d)')\" style=\"cursor:pointer\">%s</th>\n" %(i,column)
        i += 1
    res += "\t</tr>\n"

    ## Now we include each row
    for row in rows:
        res += "\t<tr class=\"row\">\n\t\t<td><a href=\"images/%s.png\" target=\"_blank\">%s</a></td>\n" %(row[0], row[0])
        if((type(row[1]) in (list, tuple)) and (len(row[1]) == len(columns))):
            for el in row[1]:
                res += "\t\t<td>%s</td>\n" %mlatex(el, "\\(", "\\)")
        else:
            res += "\t\t<td colspan=\"%d\">%s</td>\n" %(len(columns),row[1])
        res += "\t</tr>\n"
    res += "</table>\n\n"
    return res

def make_json_file(folder, columns, row, add=True):
    r'''
        Method to create a JSON file.

        This method takes the data and creates/updates the JSON file related with the model indicated.
        The user needs to provide the name of the data columns and a row of data. This *row* has the following
        format:
            * The first element has to be the name of the model. It will be used as the name of the file and
              it will also appear in the JSON data.
            * The second element has to be either an element (i.e., an error ocurred for this data) or a list of
              the exact length of the columns we have.

        THe argument ``add`` allows the user to increase the previous computed data. This means, we can extend previous
        JSON files using new data. Previous attributes with the same name of one of the columns will be overwritten and
        new attributes will be added.

        If an error is given, all the pretended attributes will be empty added and the attribute "is_valid" will be set to false.

        **WARNING**: applying this method alone may result on having different attributes in each model.
    '''
    import json
    data = {}; is_valid = True
    if(add): # we try to look for the old file
        try:
            with open(folder+row[0]+".json" , "r") as f:
                data = json.load(f)
                is_valid = data["is_valid"]
        except IOError:
            pass

    data["name"] = row[0]
    if((not (type(row[1]) in (list, tuple))) or (len(row[1]) != len(columns))): # some error during execution
        data["is_valid"] = False
        data["error"] = str(row[1])
        for column in columns:
            data[column] = data.get(column, "")
    else:
        data["is_valid"] = is_valid
        for i in range(len(columns)):
            data[columns[i]] = mlatex(row[1][i], "", "")

    ## Dumping the json file
    with open(folder+row[0]+".json", "w") as f:
        json.dump(data, f, indent=4)

    return json.dumps(data, indent=4)

def compile_json_library(folder, file):
    r'''
        Method to compile all the json files into a library

        This method takes all the json files on one folder with names from the model
        list and create a big json file with all the data compiles.
    '''
    import json
    with open(file, "w") as f:
        f.write("let data = ")
        all_data = []
        for m in AllModels:
            try:
                with open(folder + m.name() + ".json", "r") as model_file:
                    all_data += [json.load(model_file)]
            except IOError:
                pass
        json.dump(all_data, f, indent=4)

def apply_and_latex(method, file, columns, types=None, avoid_fg = False, avoid_ne = False, avoid_ie = False, verbose=True):
    r'''
        Method to apply and create a LaTeX file with the data from a method.

        This method puts together all the other methods on this package and gathers the
        data using a method for all the models and creates a LaTeX table with the
        columns described.

        See methods :func:`make_latex_table` and :func:`apply_method` for further information.
    '''
    with open(file, 'w') as f:
        dict_of_results = apply_method(method, avoid_fg, avoid_ne, avoid_ie, verbose)

        f.write("\\documentclass{article}\n")
        f.write("\\usepackage[a4paper,margin=1in,landscape]{geometry}\n")
        f.write("\\usepackage{longtable}\n")
        f.write("\n\\begin{document}\n")
        if(not avoid_fg):
            f.write("\\section*{Models with finite group}\n")
            f.write(make_latex_table(columns,dict_of_results[0].items(),types))
        if(not avoid_ne):
            f.write("\\section*{Models with non-elliptic curve}\n")
            f.write(make_latex_table(columns,dict_of_results[1].items(),types))
        if(not avoid_ie):
            f.write("\\section*{Models with infinite group and elliptic curve}\n")
            f.write(make_latex_table(columns,dict_of_results[2].items(),types))
        f.write("\\end{document}")

        if(verbose): print("Saving in file...")

        f.close()
        if(verbose): print("File saved!")

def apply_and_html(method, file, columns, types=None, avoid_fg = False, avoid_ne = False, avoid_ie = False, verbose=True):
    r'''
        Method to apply and create a HTML file with the data from a method.

        This method puts together all the other methods on this package and gathers the
        data using a method for all the models and creates a HTML table with the
        columns described.

        See methods :func:`make_html_table` and :func:`apply_method` for further information.
    '''
    with open(file, 'w') as f:
        dict_of_results = apply_method(method, avoid_fg, avoid_ne, avoid_ie, verbose)

        f.write("<!DOCTYPE html>\n")
        f.write("<html>\n")
        f.write("<head>\n")
        f.write("\t<meta charset=\"utf-8\">\n")
        f.write("\t<meta name=\"viewport\" content=\"width=device-width\">\n\n")

        f.write("\t<link rel=\"stylesheet\" href=\"./style.css\">\n")
        f.write("\t<title>Tables for Walks in the Quarter plane</title>\n")
        f.write("\t<script src=\"https://polyfill.io/v3/polyfill.min.js?features=es6\"></script>\n")
        f.write("\t<script id=\"MathJax-script\" async\n")
        f.write("\t\tsrc=\"https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-mml-chtml.js\">\n")
        f.write("\t</script>\n\n")

        f.write("\t<script src=\"https://www.w3schools.com/lib/w3.js\"></script>\n")
        f.write("\t<script src=\"http://www.w3schools.com/lib/w3data.js\"></script>\n\n")

        f.write("</head>\n")
        f.write("<body>\n")
        f.write("\t<iframe id=\"intro\" src=\"header.html\" height=\"250\" seamless=\"seamless\"></iframe>\n\n")

        results = []
        if(not avoid_fg):
            results += dict_of_results[0].items()
        if(not avoid_ne):
            results += dict_of_results[1].items()
        if(not avoid_ie):
            results += dict_of_results[2].items()
        f.write(make_html_table(columns,results,types))

        f.write("</body>\n")
        f.write("</html>")

        if(verbose): print("Saving in file...")
        f.close()
        if(verbose): print("File saved!")

def apply_and_json(method, file, columns, add=True, avoid_fg = False, avoid_ne = False, avoid_ie = False, verbose=True):
    r'''
        Method to apply and create a JSON file with the data from a method.

        This method puts together all the other methods on this package and gathers the
        data using a method for all the models and creates a JSON file with the
        columns described.

        See methods :func:`make_json_file` and :func:`apply_method` for further information.
    '''
    # Computing the folder of the file
    folder = "/".join(file.split("/")[:-1])
    folder = folder + "/" if len(folder) > 0 else ""

    dict_of_results = apply_method(method, avoid_fg, avoid_ne, avoid_ie, verbose)
    results = sum([dict_of_results[i].items() for i in range(3)], [])
    for result in results:
        make_json_file(folder, columns, result, add)

    if(verbose): print("Generated/Updated all JSON files")

    ## Combining all the json in folder
    if(verbose): print("Compiling a global JSON file...")
    compile_json_library(folder, file)
    if(verbose): print("File saved!")

def get_telescoper(m, log_level=ERROR):
    r'''
        Method that gets the telescoper of the function `b_2(x,y)` for a model.

        This method allows the input to be either a WalkModel or the name of a model. Setting the log_level to
        levels between 20 and 30 will show up the information messages that can be found on walkmodel.py and
        alggeo.py.
    '''
    from sage.misc.misc import get_verbose, set_verbose
    aux_verbose = get_verbose(); set_verbose(-1)
    dlogger = dlogging.getLogger()
    if(dlogger != None):
        aux_logging = dlogging.getLogger().level; dlogging.getLogger().setLevel(int(log_level))
    try:
        if(not isinstance(m, WalkModel)):
            m = ModelDict[m]

        b2 = m.b('y')(x=x0/x1, y=y0/y1)

        return m.telescoping(b2)
    except ValueError as e:
        dlogging.warning("Model %s has an error with the telescoper:\n%s" %(m.name(), e))
        return ("No telescoper", None)
    finally:
        set_verbose(aux_verbose)
        if(dlogger != None):
            dlogging.getLogger().setLevel(aux_logging)

def json_telescoper(m):
    t,c = get_telescoper(m)
    if(type(t) == str): # error
        return ("", "\\text{" + t + "}", "", "")
    d = var('d')
    telescoper = latex(sum(t[i]*(d**i) for i in range(len(t)))).replace("d", "\\delta")
    return (len(t)-1, telescoper, c.numerator(), c.denominator())

def telescoper_fields():
    return ("ordertelescoper",
        "telescoper",
        "numcertificatetelescoper",
        "dencertificatetelescoper")

def get_all(m, limit_time=300):
    r'''
        Method to gather information about a model of Walks in the quarter plane.

        This method returns a sequence of data that can be used later for the method
        make_####_table to create a table to show this information in a nice and friendly
        way.

        INPUT:
            * ``m``: a WalkModel to extract the information
            * ``limit_time``: maximal amount of seconds dedicated to each operation. Only some
              operations have this time limitation.

        OUTPUT:
            A list of elements describing:

            * The defining polynomials of the map `\tau` in the model `x_0`, `x_1`, `y_0`, `y_1`.
            * The order of the map `tau`.
            * The kernel equation in coordinates `x`, `y`, `z`.
            * The kernel equation in coordinates `u`, `v`, `w`.
            * The kernel equation in coordinates `x_0`, `x_1`, `y_0`, y_1`.
            * The minimal polynomials of the algebraic extension required for defining the map between the models.
            * The function `b_2(x,y)`
            * The poles of `b_2(x,y)` in the double projective space with its valuation.
            * The `\tau`-orbits of the poles of `b_2(x,y)`
            * In the case of a finite group, the *orbit sum* of `b_2(x,y)`.
            * The poles of the orbit sum of `b_2(x,y)`.
            * The neutral point in the coordinates `x_0`, `x_1`, `y_0`, `y_1` (if the curve is elliptic).
            * The point defined with `\tau(O)` in the Weierstrass coordinates (if the curve is elliptic).
            * The point defined with `\tau(O)` in the coordinates `x_0`, `x_1`, `y_0`, `y_1` (if the curve is elliptic).
            * The value of the constant `g_2` (if the curve is elliptic).
            * The value of the constant `g_3` (if the curve is elliptic).
            * The type of the model (elliptic, finite or non-elliptic)
            * The order of the telescoper of `b_2` (if it exists)
            * The telescoper of `b_2` (if it exists)
            * The certificate of the telescoper for `b_2`.

    '''
    # order of tau
    try:
        with(time_limit(limit_time)):
            order = m.order_tau() if(m.is_elliptic()) else order_morphism(m.tau('P'))
    except KeyboardInterrupt:
        order = Infinity

    b2 = m.b('y')(x=x0/x1,y=y0/y1)

    # Different models
    m_xyz = m.kernel('a'); m_x0x1y0y1 = m.kernel('p'); m_uvw = m.kernel('w') if m.is_elliptic() else "\\text{Not meaningful: not elliptic}"

    # getting extensions for the maps between models
    map_extension = m._WalkModel__field_F.defining_polynomial() if (m.is_elliptic() and m._WalkModel__field_G != WalkModel._F) else "\\text{None}"

    # gathering the poles
    if(m.is_elliptic()):
        poles = ""; pole_info_b2 = ""; pole_orbit = ""; done = False
        try:
            with(time_limit(limit_time)):
                poles = m.poles(b2, 'P')
        except KeyboardInterrupt:
            poles = "\\text{Tiemout at %s seconds}" %limit_time
            pole_info_b2 = "\\text{Tiemout at %s seconds}" %limit_time
            pole_orbit = "\\text{Not meaningful: no poles}"
            done = True
        if(not done):
            try:
                with(time_limit(limit_time)):
                    pole_info_b2 = {}
                    for pole in poles:
                        key = pole if pole.scheme().base_ring() == m.curve('P').base_ring() else (pole, pole.scheme().base_ring().base_ring().defining_polynomial())
                        pole_info_b2[key] = asymptotics(m.curve('p'), b2, pole)[0]
            except KeyboardInterrupt:
                pole_info_b2 = {}
                for pole in poles:
                    key = pole if pole.scheme().base_ring() == m.curve('P').base_ring() else (pole, pole.scheme().base_ring().base_ring().defining_polynomial())
                    pole_info_b2[key] = "??"

        if(not done):
            try:
                with(time_limit(limit_time)):
                    orbits, jumps = m.orbits(poles)
                    pole_orbit = "\\begin{array}{c}\n"
                    for i in range(len(orbits)):
                        pole_orbit += mlatex(orbits[i][0], "", "")
                        for j in range(len(jumps[i])):
                            pole_orbit += ("\\rightarrow^%d " %jumps[i][j])+ mlatex(orbits[i][j+1], "", "")
                        pole_orbit += "\\\\\n"
                    pole_orbit += "\\end{array}"
            except KeyboardInterrupt:
                pole_orbit = "\\text{Tiemout at %s seconds}" %limit_time
    else:
        poles = "\\text{Not meaningful: not elliptic}"
        pole_info_b2 = "\\text{Not meaningful: not elliptic}"
        pole_orbit = "\\text{Not meaningful: not elliptic}"

    # orbit sum of b2
    current = b2; total = 0; ptau = pullback(m.tau('p'))
    if(order < Infinity):
        orbit_sum = ""; info_poles_os = ""
        try:
            with(time_limit(limit_time)):
                for i in range(order):
                    total += current; current = ptau(current)
                orbit_sum = total
                try:
                    poles_os = m.poles(orbit_sum, 'P')
                    info_poles_os = {}
                    for pole in poles_os:
                        key = pole if pole.scheme().base_ring() == m.curve('P').base_ring() else (pole, pole.scheme().base_ring().base_ring().defining_polynomial())
                        info_poles_os[key] = asymptotics(m.curve('p'), orbit_sum, pole)[0]
                except NotImplementedError:
                    info_poles_os = "\\text{Inner error}"
        except KeyboardInterrupt:
            orbit_sum = "\\text{Timeout at %s seconds}" %limit_time
            info_poles_os = "\\text{Timeout at %s seconds}" %limit_time
    else:
        orbit_sum = "\\text{Not meaningful: infinite order}"
        info_poles_os = "\\text{Not meaningful: infinite order}"

    ## Elliptic data
    OP = ""; TW = ""; TP = ""; g2 = ""; g3 = ""
    try:
        # Important points
        OP = m.neutral_point("P") if m.is_elliptic() else "\\text{Not meaningful: not elliptic}"
        TW = m.get_point_tau("W") if m.is_elliptic() else "\\text{Not meaningful: not elliptic}"
        TP = m.get_point_tau("P") if m.is_elliptic() else "\\text{Not meaningful: not elliptic}"
        g2 = m.g2() if m.is_elliptic() else "\\text{Not meaningful: not elliptic}"
        g3 = m.g3() if m.is_elliptic() else "\\text{Not meaningful: not elliptic}"
    except Exception:
        OP = "\\text{Error computing the elliptic model}"
        TW = "\\text{Error computing the elliptic model}"
        TP = "\\text{Error computing the elliptic model}"
        g2 = "\\text{Error computing the elliptic model}"
        g3 = "\\text{Error computing the elliptic model}"

    if(m.name().find("FG") != -1):
        typ = "finite"
    elif(m.name().find("NE") != -1):
        typ = "non-elliptic"
    elif(m.name().find("wI") != -1):
        typ  = "elliptic"
    else:
        typ = "undefined"

    order_telescoper = ""; telescoper = ""; num_certificate = ""; den_certificate = ""
    try:
        with(time_limit(limit_time)):
            if(m.is_elliptic()):
                try:
                    order_telescoper, telescoper, num_certificate, den_certificate = json_telescoper(m)
                except ArithmeticError:
                    order_telescoper = "\\text{Error on telescoper}"
                    telescoper = "\\text{Error on telescoper}"
                    num_certificate = "\\text{Error on telescoper}"
                    den_certificate = "\\text{Error on telescoper}"

        if(telescoper != "" and all(other == "" for other in (order_telescoper, num_certificate, den_certificate))): # No telescoper case
            order_telescoper = "\\text{Not meaningful: no telescoper}"
            telescoper = "\\text{No telescoper}"
            num_certificate = "\\text{Not meaningful: no telescoper}"
            den_certificate = "\\text{Not meaningful: no telescoper}"

    except TimeoutException:
        order_telescoper = "\\text{Timeout at %s seconds}" %limit_time
        telescoper = "\\text{Timeout at %s seconds}" %limit_time
        num_certificate = "\\text{Timeout at %s seconds}" %limit_time
        den_certificate = "\\text{Timeout at %s seconds}" %limit_time

    return (m.tau('P').defining_polynomials(), order,
        m_xyz, str(m_xyz), m_uvw, str(m_uvw), m_x0x1y0y1, str(m_x0x1y0y1), map_extension,
        m.b('y'), str(m.b('y')), pole_info_b2, pole_orbit,
        orbit_sum, str(orbit_sum), info_poles_os,
        OP, TW, TP,
        g2, str(g2), g3, str(g3),
        typ,
        order_telescoper, telescoper, num_certificate, str(num_certificate), den_certificate, str(den_certificate))

def get_json_field():
    return ("taux0x1y0y1",
    "orderoftau",
    "kernelinxyz",
    "kernelinxyz_sage",
    "kernelinuvw",
    "kernelinuvw_sage",
    "kernelinx0x1y0y1",
    "kernelinx0x1y0y1_sage",
    "alguwtoxyz",
    "b2xy",
    "b2xy_sage",
    "polesb2valuation",
    "orbitpolesofb2",
    "orbitsumb2",
    "orbitsumb2_sage",
    "polesorbitsum",
    "neutralpointxy",
    "additionbytauinuv",
    "additionbytauinxy",
    "g2",
    "g2_sage",
    "g3",
    "g3_sage",
    "type",
    "ordertelescoper",
    "telescoper",
    "numcertificatetelescoper",
    "numcertificatetelescoper_sage",
    "dencertificatetelescoper",
    "dencertificatetelescoper_sage")

def get_json_names():
    return ("\\tau(x_0,x_1,y_0,y_1)",
    "\\text{Order of }\\tau",
    "K(x,y,z)",
    "K(u,v,w)",
    "K(x_0,x_1,y_0,y_1)",
    "\\text{Alg. For UVW }\\rightarrow\\text{ XYZ}",
    "b_2(x,y)",
    "\\text{Poles }b_2 \\rightarrow\\text{ Valuation}",
    "\\text{Orbits poles of }b_2",
    "\\text{Orbit sum }b_2",
    "\\text{Poles orbit sum}",
    "\\text{Neutral point in XY}",
    "\\text{Addition by }\\tau\\text{ in UV}",
    "\\text{Addition by }\\tau\\text{ in XY}",
    "g_2",
    "g_3",
    "\\text{Type}",
    "\\text{Order of telescoper}",
    "\\text{Telescoper } (L)",
    "\\text{Numerator of Certificate }(g)",
    "\\text{Denominator of Certificate }(g)")

def get_columns():
    return ("\\(\\tau(x_0,x_1,y_0,y_1)\\)",
    "Order of \\(\\tau\\)",
    "Kernel in XYZ",
    "Kernel in UVW",
    "Kernel in X0X1Y0Y1",
    "Alg. For UVW\\(\\rightarrow\\)XYZ",
    "\\(b_2(x,y)\\)",
    "Poles \\(b_2 \\rightarrow\\) Valuation",
    "Orbits poles of \\(b_2\\)",
    "Orbit sum \\(b_2\\)",
    "Poles orbit sum",
    "Neutral point in XY",
    "Addition by \\(\\tau\\) in UV",
    "Addition by \\(\\tau\\) in XY",
    "\\(g_2\\)",
    "\\(g_3\\)",
    "Type",
    "Order of telescoper",
    "Telescoper (\\(L\\))",
    "Numerator of Certificate (\\(g\\))",
    "Denominator of Certificate (\\(g\\))")

##########################################################################################
##########################################################################################
### AUXILIARY METODS
def print_progress_bar(iteration, total, prefix = '', suffix = '', decimals = 1, length = 100, fill = '#'):
    """
    Call in a loop to create terminal progress bar
    @params:
        iteration   - Required  : current iteration (Int)
        total       - Required  : total iterations (Int)
        prefix      - Optional  : prefix string (Str)
        suffix      - Optional  : suffix string (Str)
        decimals    - Optional  : positive number of decimals in percent complete (Int)
        length      - Optional  : character length of bar (Int)
        fill        - Optional  : bar fill character (Str)
    """
    import sys
    percent = ("{0:." + str(decimals) + "f}").format(100 * (iteration / float(total)))
    filledLength = int(length * iteration // total)
    bar = fill * filledLength + '-' * (length - filledLength)
    print("\r%s |%s| %s%% (%d/%d) %s\r" % (prefix, bar, percent, iteration, total, suffix))
    # Print New Line on Complete
    if iteration == total:
        print("")
    sys.stdout.flush()