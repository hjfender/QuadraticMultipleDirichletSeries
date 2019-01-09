import sys
from sage.all import *
from sage.rings.fraction_field_element import make_element

class FieldOfRationalFunctionsWithWeylAction(sage.rings.fraction_field.FractionField_generic):
    """
    A class encapsulating the relevant entities used to find a special invariant
    function used to construct a Quadratic Multiple Dirichlet Series, as specified
    in the paper "WEYL GROUP MULTIPLE DIRICHLET SERIES CONSTRUCTED FROM QUADRATIC
    CHARACTERS" by GAUTAM CHINTA AND PAUL E. GUNNELLS. Those entities are:
        -A root system (passed in through the constructor)
        -A root lattice (corresponding to the root system)
        -A weyl group (corresponding to the root lattice)

    The class extends from the Sage class for a generic fraction field. This allows
    a user to use the invariant function as a member of its conceptual field of
    fractions, which provides lots of additional functionality.

    Note: Because Sage does not allow the square root of a generator of a polynomial
    ring I implement the parameter variable "q" as "sqrtq" and then use "sqrtq^2"
    in the subsequent computations.

    Note: Because of numerical instabilities I cannot compute the invariant functions
    over the complex numbers. However, I can do the computations over the integers without
    affecting the end result. This is what I have implemented. When the computations complete,
    I convert the result back to the the fraction field of polynomials over complex numbers.

    Example:
        sage: RS = RootSystem(['A',2])
        sage: F = FieldOfRationalFunctionsWithAction(RS)
        sage: F
        Fraction Field of Multivariate Polynomial Ring in sqrtq, x1, x2 over Complex Field
        with 53 bits of precision endowed with an action by Weyl Group of type ['A', 2]
        (as a matrix group acting on the root lattice)
        sage: F.root_system
        Root system of type ['A', 2]
        sage: F.lattice
        Root lattice of the Root system of type ['A', 2]
        sage: F.weyl_group
        Weyl Group of type ['A', 2] (as a matrix group acting on the root lattice)
    """

    ###############################################################
    #Class related methods
    ###############################################################
    def __init__(self, root_system):
        self.root_system = root_system
        self.lattice = root_system.root_lattice()
        self.weyl_group = self.lattice.weyl_group()
        #construct the function field variables
        variables = ['sqrtq']
        for i in range(1,self.lattice.dimension() + 1):
            variables.append('x'+str(i))
        #determine phi dictionary for fast access later
        self.phi = {}
        for w in self.weyl_group.list():
            self.phi[w] = self._phi(w)
        #create computation field
        self.CF = PolynomialRing(ZZ, variables).fraction_field()
        #acted on variables for fast access later
        self.acted_variables = {}
        for i in range(1,self.lattice.dimension() + 1):
            self.acted_variables["s"+str(i)] = self._act_on_variables("s"+str(i))
            self.acted_variables["s"+str(i)+"e"+str(i)] = self._act_on_variables("s"+str(i)+"e"+str(i))
        #call parent constructor to create actual field
        sage.rings.fraction_field.FractionField_generic.__init__(self, PolynomialRing(CC, variables))

    def __str__(self):
        return (super(FieldOfRationalFunctionsWithWeylAction, self).__str__() \
                + " endowed with an action by " + str(self.weyl_group))

    def __repr__(self):
        return (super(FieldOfRationalFunctionsWithWeylAction, self).__repr__() \
                + " endowed with an action by " + str(self.weyl_group))

    ################################################################
    #Methods related to the construction of the invariant polynomial
    ################################################################
    def _delta(self):
        """
        Compute the 'Delta' polynomial defined on page 12.

        Example:
            sage: F._delta() #F is based on RootSystem(['A',2])
            -(q^2*x0^2*x1^2 - 1)*(q*x0^2 - 1)*(q*x1^2 - 1)
        """
        p = self.CF(1)
        q = self.CF('sqrtq')**2
        for a in self.lattice.positive_roots():
            cfs = a.coefficients()
            p = p * (1 - q ** sum(cfs) * self._x(2*a))
        return p

    def _j(self, w):
        """
        Compute the 'j' polynomial for a weyl group element 'w' defined
        on page 12 based on Lemma 3.8.

        Example:
            sage: w = F.weyl_group.random_element()
            sage: w
            [ 0 -1]
            [-1  0]
            sage: w.reduced_word()
            [1, 2, 1]
            sage: F_.j(w)
            -q^4*x0^4*x1^4
        """
        rw = w.reduced_word()
        variables = self.CF.variable_names()
        j = 0
        q = self.CF('sqrtq')**2
        if len(rw) == 1:
            j = -q*self.CF(variables[rw[0]])**2
        else:
            a = sum(self.phi[w])
            cfs = a.coefficients()
            j = (-1)**len(rw) * q**(sum(cfs)) * self._x(2*a)
        return j

    def _f0(self, h):
        """
        Compute the f0 part of the invariant polynomial as defined in (3.20) on page 12.
        Pass in a different function for the twisted version.
        """
        f0 = self.CF(0)
        for w in self.weyl_group.list():
            g = self._j(w) * self._act(h,w)
            f0 += g
        return f0

    def _invariant_function(self, h = None):
        """
        Compute the invariant polynomial as defined in (3.21) on page 12.
        Pass in a different function for the twisted version.
        """
        if h is None:
            h = self.CF.one()
        function = self._f0(h)/self._delta()
        return function

    def invariant_function(self, h = None):
        """
        Compute the invariant polynomial and convert it to the actual ring.
        """
        return self(self._invariant_function(h))


    ################################################################
    #Miscellaneous Rational Functions
    ################################################################
    def _x(self, a):
        """
        Generate monomial based off of a member of the root lattice
        as defined on page 8.

        Example:
            sage: a = F.lattice.random_element() #F is based on RootSystem(['A',2])
            sage: a
            -2*alpha[1]
            sage: m = F._x(a)
            sage: m
            x0^(-2)
        """
        variables = self.CF.variable_names()
        p = 1
        for i in range(1,len(variables)):
            p = p * self.CF(variables[i])**(a.coefficient(i))
        return p

    #################################################################
    #Miscellaneous Functions Related to Weyl Group
    ################################################################
    def _phi(self, w):
        """
        Find positive roots sent to negative roots by a weyl group element as
        defined on page 7.

        Note: I construct on instantiation every one of these values and store them
        in a dictionary for fast access. You shouldn't have to call this function.

        Example:
            sage: w = F.weyl_group.random_element() #F is based on RootSystem(['A',2])
            sage: w
            [ 0 -1]
            [-1  0]
            sage: w.reduced_word()
            [1, 2, 1]
            sage: F._phi(w)
            [alpha[1], alpha[2], alpha[1] + alpha[2]]
            sage: F.phi[w]
            [alpha[1], alpha[2], alpha[1] + alpha[2]]
        """
        w_roots = []
        for a in self.lattice.positive_roots():
            wa = w.action(a)
            for b in self.lattice.negative_roots():
                if wa == b:
                    w_roots.append(a)
                    break
        if len(w_roots) == 0:
            #we have to do the following to ensure that the sum of the
            #roots, in the method j, is a root lattice element
            w_roots.append(0*self.lattice.gens()[0]) 
        return w_roots

    ###############################################################
    #Methods related to the Weyl action on variables
    ###############################################################
    def _sigma(self, i, v):
        """
        Action on a list of inputs 'v', length equal to the lattice dimension,
        by the ith generator of the weyl group, i.e. the ith simple reflection,
        as defined in (3.8) on page 8.

        Example:
            sage: v = [x for x in F.variable_names()]
            sage: F._sigma(0,v) #F is based on RootSystem(['A',2])
            [1/(q*x0), sqrt(q)*x0*x1]
            sage: F._sigma(0,[1,1])
            [1/q, sqrt(q)]
        """
        w = [v[0]]
        sr = self.weyl_group.simple_reflections()
        for j in range(1, len(v)):
            if i == j:
                w.append(1/(self.CF('sqrtq')**2*v[j]))
            elif (sr[i] * sr[j])**3 == self.weyl_group.random_element_of_length(0):
                w.append(v[j]*v[i]*self.CF('sqrtq'))
            else:
                w.append(v[j])
        return w

    def _epsilon(self, i, v):
        """
        Action on symbolic variables 'v' switching sign of variables adjacent to 'xi',
        as defined in (3.10) on page 9. (Adjacency is defined on page 6)
         
        Example:
            sage: v = [x for x in F.CF.variable_names()]
            sage: F._epsilon(0,v) #F is based on RootSystem(['A',4])
            [-x0, -x1, x2, x3]
            sage: F._epsilon(0,[1,1,1,1])
            [-1, -1, 1, 1]
        """
        w = [v[0]]
        sr = self.weyl_group.simple_reflections()
        for j in range(1, len(v)):
            if i != j and (sr[i] * sr[j])**3 == self.weyl_group.random_element_of_length(0):
                w.append(-v[j])
            else:
                w.append(v[j])
        return w

    def _act_on_variables(self,pattern_string):
        """
        A helper method to ease composition of sequences of the previous two methods.

        Note: The pattern string acts left to right! This is the opposite of what is
        presented in the paper. So given 'si' is the ith simple reflection, 'ej' is the
        jth epsilon action, and 'x' is the vector of variables, the expression "si ej x" as
        appearing in (3.11) on page 9 would be written in the code as "V.act_on_variables("ejsi")."

        Example:
            sage: V.act_on_variables("e0s1") #V is based on RootSystem(['A',2])
            [x0/(sqrt(q)*x1), -1/(q*x1)]
            sage: V.act_on_variables("s1e0")
            [-x0/(sqrt(q)*x1), -1/(q*x1)]
            sage: V.act_on_variables("s1e1s1")
            [x0, -x1]
        """
        v = [self.CF(x) for x in self.CF.variable_names()]
        for i in range(0,len(pattern_string),2):
            if pattern_string[i] == 's':
                n = int(pattern_string[i+1])
                v = self._sigma(n,v)
            elif pattern_string[i] == 'e':
                n = int(pattern_string[i+1])
                v = self._epsilon(n,v)
            else:
                raise ValueError("Incorrect syntax in pattern string!")
        for x in v:
            x.reduce()
        return v

    ###############################################################
    #Methods related to the Weyl action on functions
    ###############################################################
    def _c(self, i):
        """
        Compute the 'c' polynomial defined on page 9.
        """
        q = self.CF('sqrtq')**2
        xi = self.CF('x'+str(i))
        A = (q*xi - 1)/(q*xi*(1 - xi))
        B = 1/(self.CF('sqrtq')*xi)
        c = (A + B)/2
        return c

    def _d(self, i):
        """
        Compute the 'd' polynomial defined on page 9.
        """
        q = self.CF('sqrtq')**2
        xi = self.CF('x'+str(i))
        A = (q*xi - 1)/(q*xi*(1 - xi))
        B = 1/(self.CF('sqrtq')*xi)
        d = (A - B)/2
        return d

    def _simple_action(self, f, i):
        """
        Compute the simple action on a rational function as defined in (3.14) on page 9.

        Example:
            sage: f #f is a function in the field based off of ['A', 2]
            1/(x0^4*x1^12)
            sage: WA.simple_action(f,0)
            -1/2*(1/(sqrtq*x0) + (sqrtq^2*x0 - 1)/(sqrtq^2*(x0 - 1)*x0))/(qsqrtq^4*x0^8*x1^12) + 1/2*(1/(sqrtq*x0) - (sqrtq^2*x0 - 1)/(sqrtq^2*(x0 - 1)*x0))/(sqrtq^4*x0^8*x1^12)
        """
        vars1 = self.acted_variables["s"+str(i)]
        vars2 = self.acted_variables["s"+str(i)+"e"+str(i)]
        action = self._c(i) * f(vars1) + self._d(i) * f(vars2)
        return action

    def _act(self, f, w):
        """
        Compute the weyl action extended from the simple action.

        Example:
            sage: w
            [-1  1]
            [ 0  1]
            sage: f
            (-x1^2 + x2^2 - 5*sqrtq + x2 + 1)/(-2*sqrtq^2 + 9*sqrtq*x1 - 3*sqrtq*x2 + 4*x1)
            sage: F._act(f,w)
            (3*sqrtq^11*x1^7*x2^3 + 2*sqrtq^12*x1^6*x2^2 - 3*sqrtq^11*x1^6*x2^3 - 3*sqrtq^11*x1^6*x2^2
            - 2*sqrtq^10*x1^5*x2^2 - 17*sqrtq^10*x1^5*x2 - 6*sqrtq^9*x1^5*x2^2 - 10*sqrtq^11*x1^4
            + 17*sqrtq^10*x1^4*x2 + 3*sqrtq^9*x1^5*x2 - 4*sqrtq^8*x1^5*x2^2 + 2*sqrtq^10*x1^4
            - 3*sqrtq^9*x1^4*x2 + 9*sqrtq^7*x1^4*x2^2 + 10*sqrtq^9*x1^3 + 9*sqrtq^7*x1^4*x2
            + 4*sqrtq^6*x1^4*x2^2 + 43*sqrtq^8*x1^3 - 9*sqrtq^7*x1^3*x2 + 4*sqrtq^6*x1^4*x2
            + 11*sqrtq^7*x1^3 - 4*sqrtq^6*x1^3*x2 - 4*sqrtq^6*x1^3 - 3*sqrtq^5*x1^3*x2 - 47*sqrtq^6*x1^2
            + 3*sqrtq^5*x1^2*x2 - 11*sqrtq^5*x1^2 + 4*sqrtq^4*x1^2 + 2*sqrtq^4*x1 + 9*sqrtq^3*x1
            + 4*sqrtq^2*x1 - 9*sqrtq - 4)/(-9*sqrtq^12*x1^7*x2^2 + 9*sqrtq^12*x1^6*x2^2 + 4*sqrtq^12*x1^5
            - 4*sqrtq^12*x1^4 - 36*sqrtq^9*x1^4 + 36*sqrtq^9*x1^3 - 16*sqrtq^8*x1^4 + 16*sqrtq^8*x1^3
            + 81*sqrtq^6*x1^3 - 81*sqrtq^6*x1^2 + 72*sqrtq^5*x1^3 - 72*sqrtq^5*x1^2 + 16*sqrtq^4*x1^3
            - 16*sqrtq^4*x1^2)
        """
        word = w.reduced_word()
        for i in word:
            f = self._simple_action(f, i)
        return f

    def _act_with_reduction(self, f, w):
        """
        Compute the weyl action extended from the simple action but with a reduction step added.
        """
        g = self._act(f, w)
        g.reduce()
        return g

    ###############################################################
    #Pretty print and convert to symbolic ring
    ###############################################################
    def pretty_print_CF(self, f):
        """
        Pretty print a function in the computation field. This converts "sqrtq^2"
        into "q" so the function looks like it is specified in the paper.

        sage: f = F._invariant_function()
        sage: F.pretty_print_CF(f)
        Numerator: x1*x2 - 1
        Denominator: (q*x1^2*x2^2 - 1)*(x1 - 1)*(x2 - 1)
        """
        variables = [self.CF(x) for x in self.CF.variable_names()]
        variables[0] = sqrt(var('q'))
        result = f(variables).factor()
        try:
            print "Numerator: " + str(result.numerator())
            print "Denominator: " + str(result.denominators())
        except:
            print "Result: " + str(result)

    def pretty_print(self, f):
        """
        Pretty print a function in the actual field. This converts "sqrtq^2" 
        into "q" so the function looks like it is specified in the paper.

        sage: f = F.invariant_function()
        sage: F.pretty_print(f)
        Numerator: 1.00000000000000*x1*x2 - 1.00000000000000
        Denominator: (q*x1^2*x2^2 - 1)*(x1 - 1)*(x2 - 1)
        """
        variables = [self(x) for x in self.variable_names()]
        variables[0] = sqrt(var('q'))
        result = f(variables).factor()
        try:
            print "Numerator: " + str(result.numerator())
            print "Denominator: " + str(result.denominator())
        except:
            print "Result: " + str(result)