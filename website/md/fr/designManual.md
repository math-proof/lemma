<h1>Documentation</h1>

Ce système comprend trois éléments de base : [Symbol](../?symbol=Symbol), [Function](../?symbol=Function), Theorem ;
* Un **Symbol** est un identificateur composé de lettres et de chiffres. Sa convention de nommage est celle du langage [Python](https://www.python.org/).
Il sert à définir toute variable ou symbole mathématique abstrait, par exemple :
n = Symbol(integer=True, positive=True, random=True, odd=True) désigne une variable aléatoire impaire strictement positive ;
p, q = Symbol(prime=True, even=False) indique que p et q sont des nombres premiers impairs ;
m = Symbol(integer=True, nonnegative=True) désigne un entier non négatif ;
t = Symbol(domain=Range(0, m)) désigne un entier de 0 (inclus) à m (exclus) ;
a = Symbol(integer=True, shape=(oo,)) désigne un vecteur infini d'entiers ;
b = Symbol(real=True, shape=(oo, oo)) désigne une matrice infinie de réels ;
c = Symbol(complex=True, shape=(n, n, n)) désigne un tenseur complexe de forme n × n × n ;
A = Symbol(etype=dtype.real, measurable=True) désigne un ensemble [mesurable](https://en.wikipedia.org/wiki/Measure_(mathematics)) de réels (etype = « element type ») ;
B = Symbol(etype=dtype.real, countable=True) désigne un ensemble [dénombrable](https://en.wikipedia.org/wiki/Countable_set) de réels ;
C = Symbol(etype=dtype.integer, shape=(n,)) désigne un vecteur de n ensembles d'entiers ;
Q = Symbol(etype=dtype.rational.set) désigne un ensemble dont chaque élément est un ensemble de rationnels ;

* Une **Function** désigne un calcul mathématique appliqué à d'autres symboles ou fonctions ; par exemple :
f, f1 = Function(real=True) désignent des fonctions réelles abstraites non encore définies ;
g = Function(real=True, eval=lambda x: x \* x) définit g(x) = x<sup>2</sup> ;
h = Function(etype=dtype.integer) désigne une fonction abstraite à valeurs dans l'ensemble des entiers ;
f = Function(real=True, continuous=True) désigne une fonction réelle continue en tout point ;
f = Function(real=True, differentiable=True) désigne une fonction réelle dérivable en tout point ;
f = Function(measurable=True, domain=Interval(0, 1)) désigne une fonction réelle mesurable à valeurs dans [0, 1] ;
f = Function(real=True, integrable=True) désigne une fonction réelle intégrable au sens de Lebesgue sur tout intervalle ;
ainsi que les fonctions système [cos](../?symbol=cos)(x), [sin](../?symbol=sin)(x), [tan](../?symbol=tan)(x), [log](../?symbol=log)(x), [exp](../?symbol=exp)(x), et des opérateurs plus complexes [Sum](../?symbol=Sum)\[k:a:b\](h\[k\]), [Product](../?symbol=Product)\[k:a:b\](h\[k\]), [ForAll](../?symbol=All)\[k:a:b\](h\[k\] > t\[k\]), [Exists](../?symbol=Any)\[k:a:b\](h\[k\] > t\[k\]), etc.
Ces fonctions n'effectuent pas de calculs en virgule flottante : dans une preuve mathématique, l'usage de flottants introduirait une erreur logique en mathématiques pures.
Toute valeur en preuve est une valeur mathématique au sens strict ; il n'y a pas de valeurs approchées comme en flottant ;

* Un **Theorem** désigne un théorème démontrable ou un axiome indémontrable ;
Les entrées des théorèmes sont des expression(s) ou condition(s) ; les sorties sont nécessairement des condition(s). Ils sont stockés dans une base MySQL comme banque de connaissances. Usage principal : Theorem.apply(...); par exemple :
a, b, c = Symbol(complex=True)
[Algebra.Add_Eq_0.to.And.Imply.cubic.apply](../?module=Algebra.Add_Eq_0.to.And.Imply.cubic)(Equal(x ** 3 + a * x ** 2 + b * x + c, 0), x=x) décrit la résolution d'une équation cubique dans les complexes.

Hiérarchie des ensembles numériques :
[prime](https://en.wikipedia.org/wiki/Prime_number) ⊂ [natural](https://en.wikipedia.org/wiki/Natural_number) ⊂ [integer](https://en.wikipedia.org/wiki/Integer) ⊂ extended_integer
[rational](https://en.wikipedia.org/wiki/Rational_number) ⊂ extended_rational
[real](https://en.wikipedia.org/wiki/Real_number) ⊂ [extended_real](https://en.wikipedia.org/wiki/Extended_real_number_line) ⊂ [hyper_real](https://en.wikipedia.org/wiki/Hyperreal_number) ⊂ [super_real](https://en.wikipedia.org/wiki/Superreal_number)
[complex](https://en.wikipedia.org/wiki/Complex_number) ⊂ [extended_complex](https://en.wikipedia.org/wiki/Riemann_sphere) ⊂ [hyper_complex](https://en.wikipedia.org/wiki/Hypercomplex_number) ⊂ [super_complex](https://en.wikipedia.org/wiki/Surreal_number#Surcomplex_numbers)
[integer](https://en.wikipedia.org/wiki/Integer) ⊂ [rational](https://en.wikipedia.org/wiki/Rational_number) ⊂ [real](https://en.wikipedia.org/wiki/Real_number) ⊂ [complex](https://en.wikipedia.org/wiki/Complex_number)
extended_integer ⊂ extended_rational ⊂ [extended_real](https://en.wikipedia.org/wiki/Extended_real_number_line) ⊂ [extended_complex](https://en.wikipedia.org/wiki/Riemann_sphere)
[hyper_real](https://en.wikipedia.org/wiki/Hyperreal_number) ⊂ [hyper_complex](https://en.wikipedia.org/wiki/Hypercomplex_number)
[super_real](https://en.wikipedia.org/wiki/Superreal_number) ⊂ [super_complex](https://en.wikipedia.org/wiki/Surreal_number#Surcomplex_numbers)
