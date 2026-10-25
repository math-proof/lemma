/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry10ZetaSide.lean -/

/-
Author: @akiezun, Avocado
-/

import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Lemma.Nat.LSeries.RiemannZeta
/-!
# Ramanujan's Notebooks, Part I, Chapter 7, Entry 10: the zeta side

The right side `(1 - n^(r+1)) ζ(-r)` shared by the Entry 10 identities of B. C. Berndt,
*Ramanujan's Notebooks, Part I* (Springer, 1985), Chapter 7, and its meromorphicity. It lives in
the `Entry10Zeta4` namespace because that entry's frozen statement pins this name.
-/


namespace MathlibExt.Analysis.Ramanujan.Part1Ch7

namespace Entry10Zeta4

noncomputable section

def chapter7Entry10ZetaSide (n : ℕ) (r : ℂ) : ℂ :=
  (1 - Complex.cpow (n : ℂ) (r + 1)) * riemannZeta (-r)

end
end Entry10Zeta4
end MathlibExt.Analysis.Ramanujan.Part1Ch7
