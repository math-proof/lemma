import Mathlib
import sympy.Basic
open MvPolynomial


/--
[eval_zero_of_homogeneous_pos_deg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SyzygiesKoszul.lean)
-/
@[path]
private lemma main
  [Field k]
  {n : ℕ}
  {f : MvPolynomial (Fin n) k}
  {d : ℕ}
-- given
  (hd : 0 < d)
  (hhom : ∀ (m : Finsupp (Fin n) ℕ), f.coeff m ≠ 0 → (m.sum fun _ e => e) = d) :
-- imply
  eval (0 : Fin n → k) f = 0 := by
-- proof
  simp only [eval_zero]
  rw [constantCoeff_eq]
  by_contra h
  have := hhom 0 h
  simp at this
  omega


-- created on 2026-10-24
