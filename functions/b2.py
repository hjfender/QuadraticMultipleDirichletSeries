from weyl_group_multiple_dirichlet_series_v4.field_of_rational_functions_with_weyl_action import *

R = RootSystem(['B', 2]);

F = FieldOfRationalFunctionsWithWeylAction(R);

sqrtq = F.CF.gen(0);
x1 = F.CF.gen(1);
x2 = F.CF.gen(2);
f1 = (sqrtq**10*x1**5*x2**7 - sqrtq**10*x1**5*x2**6 - sqrtq**10*x1**4*x2**7
+ sqrtq**10*x1**4*x2**6 + sqrtq**8*x1**5*x2**5 + sqrtq**8*x1**3*x2**7
- sqrtq**8*x1**4*x2**5 - sqrtq**8*x1**3*x2**6 + sqrtq**6*x1**3*x2**5
- sqrtq**6*x1**2*x2**4 + sqrtq**4*x1**2*x2**3 + sqrtq**4*x1*x2**4
- sqrtq**4*x1**2*x2**2 - sqrtq**2*x1*x2**3 + sqrtq**2*x1**2*x2 + sqrtq**2*x1*x2**2
- x1*x2 + 1)/((sqrtq**6*x1**2*x2**4 - 1)*(sqrtq**2*x1*x2
+ 1)*(sqrtq**2*x1*x2 - 1)*(x1 - 1)*(x2 - 1));
f2 = F(f1);