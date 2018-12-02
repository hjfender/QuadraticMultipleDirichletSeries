from field_of_rational_functions_with_weyl_action import *

R = RootSystem(['A', 1]);

F = FieldOfRationalFunctionsWithWeylAction(R);

x1 = F.gen(1);
f = 1/(-x1+1);
f = F(f);