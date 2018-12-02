from field_of_rational_functions_with_weyl_action import *

R = RootSystem(['A', 2]);

F = FieldOfRationalFunctionsWithWeylAction(R);

sqrtq = F.gen(0);
x1 = F.gen(1);
x2 = F.gen(2);
f = (x1*x2-1)/((sqrtq**2*x1**2*x2**2-1)*(x1-1)*(x2-1));
f = F(f);