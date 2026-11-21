<h1>Documentation</h1>

This system is comprised of three basic elements: [Symbol](../?symbol=Symbol), [Function](../?symbol=Function), Theorem; 
* Symbol is an identifier composed of a series of alphabets and digits. Its naming convention is the same as that of [Python](https://www.python.org/) programming language.   
It is used to define any abstract mathematical symbol or variable, for instance:     
n = Symbol(integer=True, positive=True, random=True, odd=True), denotes an odd positive random variable,  
p, q = Symbol(prime=True, even=False) denotes that p is an odd prime number, so is q;     
m = Symbol(integer=True, nonnegative=True) denotes a non-negative integer,   
t = Symbol(domain=Range(0, m)) denotes an integer ranging from 0 (including) to m (excluding);  
a = Symbol(integer=True, shape=(oo,)) denotes an infinitely large vector of integers;   
b = Symbol(real=True, shape=(oo, oo)) denotes an infinitely large matrix of reals;   
c = Symbol(complex=True, shape=(n, n, n)) denotes a complex tensor of shape n * n * n;   
A = Symbol(etype=dtype.real, measurable=True) denotes a [measurable](https://en.wikipedia.org/wiki/Measure_(mathematics)) set of reals, wherein etype is abbreviated from "element type";  
B = Symbol(etype=dtype.real, countable=True) denotes a [countable](https://en.wikipedia.org/wiki/Countable_set) set of reals;  
C = Symbol(etype=dtype.integer, shape=(n,)) denotes a vector of n sets of integers;     
Q = Symbol(etype=dtype.rational.set) denotes a set, the element of which is a set of rationals;    

* Function denotes a certain mathematical computations on other symbols or functions; for instance:  
f, f1 = Function(real=True) denotes that f, f1 are all abstract real function whose definition is unknown yet;   
g = Function(real=True, eval=lambda x: x \* x) denotes a real-valued function defined as: g(x) = x<sup>2</sup>;     
h = Function(etype=dtype.integer) denotes an abstract function whose return value is of type: integer set;  
f = Function(real=True, continuous=True) denotes a real-valued function continuous at any given point;    
f = Function(real=True, differentiable=True) denotes a real-valued function differentiable at any given point;    
f = Function(measurable=True, domain=Interval(0, 1)) denotes a measurable real-valued function whose value lies within domain [0, 1];    
f = Function(real=True, integrable=True) denotes a real-valued function Lebesgue-integrable at any given interval;    
as well as system built-in function, such as [cos](../?symbol=cos)(x), [sin](../?symbol=sin)(x), [tan](../?symbol=tan)(x), [log](../?symbol=log)(x), [exp](../?symbol=exp)(x), and some more complex operators [Sum](../?symbol=Sum)\[k:a:b\](h\[k\]), [Product](../?symbol=Product)\[k:a:b\](h\[k\]), [ForAll](../?symbol=All)\[k:a:b\](h\[k\] > t\[k\]), [Exists](../?symbol=Any)\[k:a:b\](h\[k\] > t\[k\]), etc.  
All these functions will not perform any float-point calculations as usual, since during the process of mathematical proving, any involvement of calculations with float-point values will yield a logic error in pure mathematics.    
Every value in mathematical proving is in strict sense mathematical value, there is no concept of approximate values like float-pointing values;      


* Theorem denotes a theorem that is provable or an axiom that is unprovable ;      
The inputs of theorems must be expression(s) or condition(s), its outputs are necessarily condition(s). It is stored in a mysql database as a theorem knowledge bank. Its main usage is as follows: Theorem.apply(...); for instance:    
a, b, c = Symbol(complex=True)  
[Algebra.Add_Eq_0.to.And.Imply.cubic.apply](../?module=Algebra.Add_Eq_0.to.And.Imply.cubic)(Equal(x ** 3 + a * x ** 2 + b * x + c, 0), x=x), denotes the determination process of a cubic equation within the domain of Complexes.     

The number system set is defined as  
[prime](https://en.wikipedia.org/wiki/Prime_number) ⊂ [natural](https://en.wikipedia.org/wiki/Natural_number) ⊂ [integer](https://en.wikipedia.org/wiki/Integer) ⊂ extended_integer  
[rational](https://en.wikipedia.org/wiki/Rational_number) ⊂ extended_rational  
[real](https://en.wikipedia.org/wiki/Real_number) ⊂ [extended_real](https://en.wikipedia.org/wiki/Extended_real_number_line) ⊂ [hyper_real](https://en.wikipedia.org/wiki/Hyperreal_number) ⊂ [super_real](https://en.wikipedia.org/wiki/Superreal_number)  
[complex](https://en.wikipedia.org/wiki/Complex_number) ⊂ [extended_complex](https://en.wikipedia.org/wiki/Riemann_sphere) ⊂ [hyper_complex](https://en.wikipedia.org/wiki/Hypercomplex_number) ⊂ [super_complex](https://en.wikipedia.org/wiki/Surreal_number#Surcomplex_numbers)  
[integer](https://en.wikipedia.org/wiki/Integer) ⊂ [rational](https://en.wikipedia.org/wiki/Rational_number) ⊂ [real](https://en.wikipedia.org/wiki/Real_number) ⊂ [complex](https://en.wikipedia.org/wiki/Complex_number)  
extended_integer ⊂ extended_rational ⊂ [extended_real](https://en.wikipedia.org/wiki/Extended_real_number_line) ⊂ [extended_complex](https://en.wikipedia.org/wiki/Riemann_sphere)  
[hyper_real](https://en.wikipedia.org/wiki/Hyperreal_number) ⊂ [hyper_complex](https://en.wikipedia.org/wiki/Hypercomplex_number)  
[super_real](https://en.wikipedia.org/wiki/Superreal_number) ⊂ [super_complex](https://en.wikipedia.org/wiki/Surreal_number#Surcomplex_numbers)
