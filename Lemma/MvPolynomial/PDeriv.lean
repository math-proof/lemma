import Mathlib
import sympy.Basic
import Theorem.Algebra.MvPolynomial.PDeriv.Part2
open MvPolynomial

namespace MvPolynomial

/--
[pderiv_comm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/MvPolynomial/PDeriv.lean)
-/
@[path]
lemma pderiv_comm
  [CommSemiring k]
-- given
  (i j : σ) (p : MvPolynomial σ k) :
-- imply
  pderiv i (pderiv j p) = pderiv j (pderiv i p) := by
-- proof
  by_cases h : i = j
  · subst j
    rfl
  · ext s
    simp only [coeff_pderiv]
    rw [show s + Finsupp.single i 1 + Finsupp.single j 1 =
      s + Finsupp.single j 1 + Finsupp.single i 1 by abel]
    simp [h, Ne.symm h]
    ring

end MvPolynomial

namespace MvPolynomial

/--
[mixedDifferential_nil](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/MvPolynomial/PDeriv.lean)
-/
@[path]
lemma mixedDifferential_nil
  [CommRing k]
-- given
  (p : MvPolynomial σ k) :
-- imply
  mixedDifferential [] p = p := by
-- proof
  rfl

end MvPolynomial

namespace MvPolynomial

/--
[mixedDifferential_cons](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/MvPolynomial/PDeriv.lean)
-/
@[path]
lemma mixedDifferential_cons
  [CommRing k]
-- given
  (i : σ) (iis : List σ) (p : MvPolynomial σ k) :
-- imply
  mixedDifferential (i :: iis) p = mixedDifferential iis (p - pderiv i p) := by
-- proof
  rfl

end MvPolynomial

namespace MvPolynomial

/--
[mixedDifferential_eq_of_perm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/MvPolynomial/PDeriv.lean)
-/
@[path]
lemma mixedDifferential_eq_of_perm
  [CommRing k]
-- given
  {iis js : List σ} (h : iis.Perm js) (p : MvPolynomial σ k) :
-- imply
  mixedDifferential iis p = mixedDifferential js p := by
-- proof
  induction h generalizing p with
  | nil => rfl
  | cons i h ih =>
    rw [mixedDifferential_cons, mixedDifferential_cons]
    exact ih _
  | swap i j is =>
    rw [mixedDifferential_cons, mixedDifferential_cons, mixedDifferential_cons,
      mixedDifferential_cons]
    congr 1
    rw [map_sub, map_sub, pderiv_comm]
    abel
  | trans h₁ h₂ ih₁ ih₂ => exact (ih₁ p).trans (ih₂ p)
  exact h

end MvPolynomial

namespace MvPolynomial

/--
[mixedDifferential_append](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/MvPolynomial/PDeriv.lean)
-/
@[path]
lemma mixedDifferential_append
  [CommRing k]
-- given
  (iis js : List σ) (p : MvPolynomial σ k) :
-- imply
  mixedDifferential (iis ++ js) p = mixedDifferential js (mixedDifferential iis p) := by
-- proof
  simp only [mixedDifferential, List.foldl_append]

end MvPolynomial

namespace MvPolynomial

/--
[pderiv_mixedDifferential](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/MvPolynomial/PDeriv.lean)
-/
@[path]
lemma pderiv_mixedDifferential
  [CommRing k]
-- given
  (i : σ) (iis : List σ) (p : MvPolynomial σ k) :
-- imply
  pderiv i (mixedDifferential iis p) = mixedDifferential iis (pderiv i p) := by
-- proof
  induction is generalizing p with
  | nil => rfl
  | cons j js ih =>
    rw [mixedDifferential_cons, mixedDifferential_cons, ih]
    congr 1
    rw [map_sub, pderiv_comm]

end MvPolynomial

-- created on 2026-10-09
-- updated on 2026-10-23
