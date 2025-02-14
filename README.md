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
## Definitions
Grassmann varibles (numbers) satisfy anticommutation relations

$$
\theta_i\ \theta_j = -\ \theta_j\ \theta_i\ .
$$

This implies that each individual varaible is nilpotent: $\theta_i^2 = 0$. The general element of a Grassmann algebra is given by a product of monomials of $\theta_i$ with regular (bosonic) prefactors:

$$
X = \sum\limits_n \sum\limits_{i_1\ldots i_n} c_{i_1\ldots i_n}\ \theta_1\ \ldots\ \theta_n\ .
$$

This package enables efficient multiplication, integration (= differentiation), and exponentiation of these objects.

## Usage
All Grassmann variables are encoded as arguments of the ``FF`` function. This function automatically sorts them into their natural order while correctly handling the signs that arise from permutations. The expressions processed by this package take the form of linear combinations of ``FF`` functions with arbitrary commuting prefactors. For example, in the following expression:
```mathematica
X = FF[a,b] + c FF[d]
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
For large-scale calculations, one might use the ``ParallelCircleTimes`` function instead.

This package also supports matrix multiplication with Grassmann-valued entries via the ``GDot`` and ``ParallelGDot`` commands. Additionally, Grassmann integration is implemented through the ``GIntegrate`` function:
```mathematica
GIntegrate[expr, {\[Theta][1], ... , \[Theta][n]}, norm]
```
evaluates the following integral

$$
\int d\theta_1\ \ldots\ d\theta_n\ expr\ .
$$

If only a single integration is required, the curly brackets in the second argument can be omitted. The ``norm`` argument is optional and allows modification of the baseline definition:

$$
\int d\theta\ \theta = norm\ .
$$

By default, ``norm = 1``.
Finally, the package allows for the exponentiation of Grassmann variable expressions using the ``GExp`` command.
