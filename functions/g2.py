from weyl_group_multiple_dirichlet_series_v4.field_of_rational_functions_with_weyl_action import *

R = RootSystem(['G', 2]);

F = FieldOfRationalFunctionsWithWeylAction(R);

sqrtq = F.CF.gen(0);
x1 = F.CF.gen(1);
x2 = F.CF.gen(2);
f1 = (sqrtq**28*x1**18*x2**10 - sqrtq**24*x1**17*x2**9 + sqrtq**24*x1**17*x2**8
+ sqrtq**24*x1**16*x2**9 - sqrtq**24*x1**16*x2**8 - sqrtq**22*x1**15*x2**9
+ sqrtq**22*x1**15*x2**8 + sqrtq**22*x1**14*x2**9 - sqrtq**22*x1**14*x2**8
- sqrtq**20*x1**13*x2**9 + sqrtq**20*x1**13*x2**8 + sqrtq**20*x1**12*x2**9
- sqrtq**20*x1**12*x2**8 + sqrtq**16*x1**11*x2**7 - sqrtq**16*x1**11*x2**6
- sqrtq**16*x1**10*x2**7 + sqrtq**16*x1**10*x2**6 + sqrtq**14*x1**11*x2**5
+ sqrtq**14*x1**9*x2**7 - sqrtq**14*x1**11*x2**4 - sqrtq**14*x1**10*x2**5
- sqrtq**14*x1**9*x2**6 - sqrtq**14*x1**8*x2**7 + sqrtq**14*x1**10*x2**4
+ sqrtq**14*x1**8*x2**6 + sqrtq**12*x1**11*x2**3 + sqrtq**12*x1**9*x2**5
+ sqrtq**12*x1**7*x2**7 - sqrtq**12*x1**10*x2**3 - sqrtq**12*x1**9*x2**4
- sqrtq**12*x1**8*x2**5 - sqrtq**12*x1**7*x2**6 + sqrtq**12*x1**8*x2**4
+ sqrtq**10*x1**9*x2**3 + sqrtq**10*x1**7*x2**5 - sqrtq**10*x1**8*x2**3
- sqrtq**10*x1**7*x2**4 + sqrtq**8*x1**7*x2**3 - sqrtq**8*x1**6*x2**2
+ sqrtq**6*x1**6*x2 + sqrtq**6*x1**5*x2**2 - sqrtq**6*x1**4*x2**2
- sqrtq**4*x1**5*x2 + sqrtq**4*x1**4*x2 + sqrtq**4*x1**3*x2**2
- sqrtq**4*x1**2*x2**2 - sqrtq**2*x1**3*x2 + sqrtq**2*x1**2*x2 + sqrtq**2*x1*x2**2
- x1*x2 + 1)/((sqrtq**10*x1**6*x2**4 - 1)*(sqrtq**6*x1**4*x2**2 - 1)*(sqrtq**4*x1**3*x2 + 1)
*(sqrtq**4*x1**3*x2 - 1)*(sqrtq**2*x1*x2 + 1)*(sqrtq**2*x1*x2 - 1)*(x1 - 1)*(x2 - 1));
f2 = F(f1);