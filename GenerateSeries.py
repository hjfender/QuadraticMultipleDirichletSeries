#!/usr/bin/env sage -python

###############################################################################
# A script to generate multivariate power series expansion of invariant
# functions
#
# Change the Paramaters below to generate different series
###############################################################################
from functions import b3 as func

series_length = 10
###############################################################################

F = func.F
f = func.f1

sqrtq = var('sqrtq')
variables = []
variables.append(sqrtq)

for i in range(1,len(F.gens())):
    variables.append(var('x'+str(i)))

g = f(*variables)

def recursivelyMultiply(coeffs,j):
    series = 0
    if j < len(variables)-1:
        for c in coeffs:
            tempcoeffs = c[0].series(variables[j+1],series_length).coefficients()
            series += recursivelyMultiply(tempcoeffs,j+1)*variables[j]**c[1]
    else:
        for c in coeffs:
            series += c[0]*variables[j]**c[1]
    return series

cs = g.series(variables[1], series_length).coefficients()
series = recursivelyMultiply(cs,1)
series = series.expand().simplify()

print series