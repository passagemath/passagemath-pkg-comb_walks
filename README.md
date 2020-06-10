# **Walk Models with elliptic kernel function** 

`comb_walks` is a Sage package for understanding and getting data for generating functions of Walks in the 
Quarter plane where the kernel function describes an elliptic curve. However, the code is implemented in such
a general way that it also allows the user to explore the models with rational kernel curve.

## **1. Installing the package**
You can install the code using the following `sage -pip` command:
   
   `sage -pip [--user] install git+https://gitlab.inria.fr/discretewalks/comb_walks.git`

Or you can also install the package from a local copy of the repository (after cloning it)
running the command

   `make install`

or using the `sage -pip` command on the repository:

   `sage -pip [--user] install .`
   
## **2. Using the package**

Once the package is installed on the system, the user can load the package and all its functionality
with the sage command

   `from comb_walks import *`

For further information, the user can compile its own version of the documentation running 
`make doc` and check there all the documentation and tests of the code.

For accessing the documentation, the user can also access the website

   <https://discretewalks.gitlabpages.intia.fr/comb_walks/docs/>

## **3. Extra requirements**

There are no extra requirements to running this package. If any dependencies errors are found, please contact the owners for future fixing.
