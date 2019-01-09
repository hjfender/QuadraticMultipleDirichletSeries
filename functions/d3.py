from weyl_group_multiple_dirichlet_series_v4.field_of_rational_functions_with_weyl_action import *

R = RootSystem(['D', 3]);

F = FieldOfRationalFunctionsWithWeylAction(R);

sqrtq = F.CF.gen(0);
x1 = F.CF.gen(1);
x2 = F.CF.gen(2);
x3 = F.CF.gen(3);
f1 = (sqrtq**2*x1**3*x2**2*x3**2 - sqrtq**2*x1**2*x2**2*x3 - sqrtq**2*x1**2*x2*x3**2+ sqrtq**2*x1**2*x2*x3 + x1*x2*x3 - x1*x2 - x1*x3+ 1)/((sqrtq**2*x1**2*x2**2 - 1)*(sqrtq**2*x1**2*x3**2 - 1)*(sqrtq**2*x1*x2*x3+ 1)*(sqrtq**2*x1*x2*x3 - 1)*(x1 - 1)*(x2 - 1)*(x3 - 1));
f2 = F(f1);