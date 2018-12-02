from field_of_rational_functions_with_weyl_action import *

R = RootSystem(['D', 2]);

F = FieldOfRationalFunctionsWithWeylAction(R);

x1 = F.gen(1);
x2 = F.gen(2);
f = (x2 - 1)**(-1) * (x1 - 1)**(-1);
f = F(f);