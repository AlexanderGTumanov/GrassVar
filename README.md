# Grassmann variables for Mathematica
An implementation of Grassmann anticommuting variables in Wolfram Mathematica.
## Installation
Clone this repository using
```console
git clone https://github.com/AlexanderGTumanov/grassmann-variables-for-mathematica.git
```
This will create a new directory ``grassmann-variables-for-mathematica`` in the current working directory. In your notebook file, add
```mathematica
SetDirectory["location_of_the_grassmann-variables-for-mathematica_folder"];
<<GrassmannVariables`;
```
## Usage
All Grassmann variables are encoded as arguments of the ``FF`` function. This function automatically sorts them into their natural order while correctly handling the signs that arise from permutations. The expressions processed by this package take the form of linear combinations of ``FF`` functions with arbitrary commuting prefactors. For example, in the following expression:
```mathematica
FF[a,b] + c FF[d]
```
the variables ``a``, ``b``, and ``d`` are treated as anticommuting, while ``c`` is treated as a standard bosonic variable.
Multiplication of such expressions is performed using the ``CircleTimes`` operator: 
```mathematica
CircleTimes[X[1], X[2], ..., X[n]]
```
or equivalently,
```mathematica
X[1] \[CircleTimes] X[2] \[CircleTimes] ... \[CircleTimes] X[n]
```
This package also supports matrix multiplication with Grassmann-valued entries via the ``GDot`` command.

Additionally, Grassmann integration is implemented through the ``GIntegrate`` function:
```mathematica
GIntegrate[expr, {a[1], ... , a[n]}, phase]
```
evaluates the following integral

$$
\int expr\ da_1\ \ldots\ da_n\ .
$$

If only a single integration is required, the curly brackets in the second argument can be omitted. The phase argument is optional and allows modification of the baseline definition:

$$
\int a\ da = phase\ .
$$

By default, ``phase = 1``.
Finally, the package provides support for exponentiation using the ``GExp`` command.
