import Mathlib
import Initialize.Tactic.Attr.Basic
open UpperHalfPlane ModularGroup
open scoped Modular


/--
Points in the fundamental domain have imaginary part at least sqrt(3)/2.
-/
@[path]
private lemma main
  {τ : ℍ}
-- given
  (h : τ ∈ 𝒟) :
-- imply
  Real.sqrt 3 / 2 ≤ τ.im := by
-- proof
  have h1 : 3 ≤ 4 * τ.im ^ 2 := three_le_four_mul_im_sq_of_mem_fd h
  have h2 : Real.sqrt 3 ≤ 2 * τ.im := by
    rw [Real.sqrt_le_left (by linarith [τ.im_pos])]
    nlinarith
  linarith


-- created on 2026-10-24
