from weyl_group_multiple_dirichlet_series_v4.field_of_rational_functions_with_weyl_action import *

R = RootSystem(['A', 4]);

F = FieldOfRationalFunctionsWithWeylAction(R);

sqrtq = F.CF.gen(0);
x1 = F.CF.gen(1);
x2 = F.CF.gen(2);
x3 = F.CF.gen(3);
x4 = F.CF.gen(4);
f1 = (sqrtq**4*x1**2*x2**4*x3**4*x4**2 - sqrtq**4*x1**2*x2**4*x3**3*x4- sqrtq**4*x1**2*x2**3*x3**3*x4**2 - sqrtq**4*x1*x2**3*x3**4*x4**2+ sqrtq**4*x1**2*x2**3*x3**3*x4 + sqrtq**4*x1*x2**3*x3**3*x4**2+ sqrtq**2*x1**2*x2**3*x3**2*x4 + sqrtq**2*x1*x2**3*x3**3*x4+ sqrtq**2*x1*x2**2*x3**3*x4**2 - sqrtq**2*x1**2*x2**3*x3**2- sqrtq**2*x1**2*x2**2*x3**2*x4 - sqrtq**2*x1*x2**3*x3**2*x4- sqrtq**2*x1*x2**2*x3**3*x4 - sqrtq**2*x1*x2**2*x3**2*x4**2- sqrtq**2*x2**2*x3**3*x4**2 + sqrtq**2*x1**2*x2**2*x3 + sqrtq**2*x1*x2**2*x3**2+ sqrtq**2*x1*x2**2*x3*x4 + sqrtq**2*x1*x2*x3**2*x4 + sqrtq**2*x2**2*x3**2*x4+ sqrtq**2*x2*x3**2*x4**2 - sqrtq**2*x1*x2**2*x3 - sqrtq**2*x1*x2*x3*x4- sqrtq**2*x2*x3**2*x4 - x1*x2*x3 - x2*x3*x4 + x1*x2+ x2*x3 + x3*x4 - 1)*(sqrtq**2*x1*x2*x3*x4 - 1)/((sqrtq**6*x1**2*x2**2*x3**2*x4**2- 1)*(sqrtq**2*x1**2*x2**2 -1)*(sqrtq**2*x2**2*x3**2 - 1)*(sqrtq**2*x3**2*x4**2- 1)*(sqrtq**2*x1*x2*x3 + 1)*(sqrtq**2*x1*x2*x3 - 1)*(sqrtq**2*x2*x3*x4+ 1)*(sqrtq**2*x2*x3*x4 - 1)*(x1 - 1)*(x2- 1)*(x3 - 1)*(x4 - 1));
f2 = F(f1);