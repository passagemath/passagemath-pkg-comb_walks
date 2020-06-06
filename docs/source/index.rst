=================================
Walks Models in the Quarter Plane
=================================

This is a the documentation that can be found inside the code
of the package ``daeg1``.

This package offers a unified interface for working with generating functions
and related object to Walks in the Quarter Plane. Assume we have a set

.. MATH::

    \mathcal{S} \subset \{-1,0,1\}^2 \setminus \{(0,0)\}

of, so called, valid steps. A walk according to `\mathcal{S}` is a series of 
points in `\mathbb{Z}^2` `P_0=(0,0), P_1, \ldots, P_n` such that for all `k \in \{1,...,n\}`:

.. MATH::

    P_n - P_{n-1} \in \mathcal{S}.

We also say that the length of such walk is `n`.

Let now be `q_{i,j,k}^{\mathcal{S}}` be the number of walks of length `n`that starts at `(0,0)`
and ends at `(i,j)`. Consider then the generating function:

.. MATH::

    Q_{\mathcal{S}}(x,y,t) = \sum_{i,j,k \geq 0} q_{i,j,k}^{\mathcal{S}} x^i y^j t^k \in \mathbb{Q}[x,y][[t]].

This package will allows the user to extract information of `Q_{\mathcal{S}}` providing an easy interface to
create Walk models (see class :class:`~daeg1.walkmodel.WalkModel`).

For using this package, use the import command::

    from daeg1 import *

The use of this package on the main unweighted walks models can be seeing in the `main webpage <https://anjimene.gitlabpages.inria.fr/da-equations-genus-1>`_.

This code is under the terms of GNU General Public License version 3.

This package was partially funded by the Austrian Science Fund (FWF): W1214-N15, project DK15.

It was also supported in part by the ANR `DeRerumNatura <https://specfun.inria.fr/chyzak/DeRerumNatura/>`_ project, grant ANR-19-CE40-0018 of the 
French Agence Nationale de la Recherche.


DAEG1 
===========

.. toctree::
   :maxdepth: 1

   alggeo
   walkmodel
   
Indices and Tables
==================

* :ref:`genindex`
* :ref:`modindex`
* :ref:`search`
* `Results web <https://anjimene.gitlabpages.inria.fr/da-equations-genus-1>`_
