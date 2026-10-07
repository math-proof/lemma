import sympy.concrete.continuant

/-!
SymPy's continued fraction `alpha` (`Lemma/Finset/Alpha/gt/Zero.py`):
`alpha(x[:1]) = x[0]`, `alpha(x[:n]) = x[0] + 1 / alpha(x[1:n])`; the multi-argument form
`alpha(x[:n], y, …)` is `alpha` of the concatenated argument list.
Here the argument is a `List`; `alpha [] = 0` is a junk value.
-/

namespace Continuant

def alpha {R : Type*} [Field R] : List R → R
  | [] => 0
  | [a] => a
  | a :: b :: l => a + 1 / alpha (b :: l)

end Continuant
