reset()

print "Retrieving the invariant function for A2..."
load('functions/a2.py');
print f

print ""

precision = 5

sqrtq = var('sqrtq')
t = var('t')
s = var('s')
z = 0;
for a in range(1,precision):
    for b in range(1,precision):
        z = 0
        z += f(sqrtq, sqrtq^(a*t), sqrtq^(b*s)) / (sqrtq^(2*a*t + 2*b*s));

print "Quadratic Multiple Dirichlet Series with precision " + str(precision) + "..."
print z 