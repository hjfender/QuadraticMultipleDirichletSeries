from weyl_group_multiple_dirichlet_series_v4.field_of_rational_functions_with_weyl_action import *

R = RootSystem(['A', 1]);

F = FieldOfRationalFunctionsWithWeylAction(R);

x1 = F.CF.gen(1);
f1 = 1/(-x1+1);
f2 = F(f1);