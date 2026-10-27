import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.GeneralizedBellPolynomial
open scoped BigOperators
open MetaMathlibExt


namespace MetaMathlibExt

/--
[genStirling_zero_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/GeneralizedBellPolynomial.lean)
-/
@[path]
lemma genStirling_zero_zero
  [CommRing R]
  {s h : R} :
-- imply
  genStirling s h 0 0 = 1 :=
-- proof
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[genStirling_zero_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/GeneralizedBellPolynomial.lean)
-/
@[path]
lemma genStirling_zero_succ
  [CommRing R]
  {s h : R}
  {k : ℕ} :
-- imply
  genStirling s h 0 (k + 1) = 0 :=
-- proof
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[genStirling_succ_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/GeneralizedBellPolynomial.lean)
-/
@[path]
lemma genStirling_succ_zero
  [CommRing R]
  {s h : R}
  {n : ℕ} :
-- imply
  genStirling s h (n + 1) 0 = 0 :=
-- proof
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[genStirling_succ_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/GeneralizedBellPolynomial.lean)
-/
@[path]
lemma genStirling_succ_succ
  [CommRing R]
  {s h : R}
  {n k : ℕ} :
-- imply
  genStirling s h (n + 1) (k + 1) = genStirling s h n k +
      h * ((↑(k + 1) : R) + s * (↑(n - (k + 1)) : R)) *
        genStirling s h n (k + 1) :=
-- proof
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[genBellPolynomial_eval_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/GeneralizedBellPolynomial.lean)
-/
@[path]
lemma genBellPolynomial_eval_one
  [CommRing R]
  {s h : R}
  {n : ℕ} :
-- imply
  genBellPolynomial s h n 1 = genBellNumber s h n := by
-- proof
  simp [genBellPolynomial, genBellNumber]

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-26
