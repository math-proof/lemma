import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.MathlibExtTest.FieldTheory.Finite.PermutationPolynomial


/--
[bijective_add_const_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/FieldTheory/Finite/PermutationPolynomial.lean)
is bijective on `ZMod 5`. -/
@[path]
private lemma bijective_add_const_mul {c : ZMod 5} (hc : (1 : ZMod 5) + c ≠ 0) :
  Function.Bijective fun x : ZMod 5 => x + c * x := by
  have hfun : (fun x : ZMod 5 => x + c * x) =
    fun x => ((1 : ZMod 5) + c) * x := by
    funext x
    rw [add_mul, one_mul]
  rw [hfun]
  constructor
  · intro a b hab
    exact mul_left_cancel₀ hc hab
  · intro y
    refine ⟨((1 : ZMod 5) + c)⁻¹ * y, ?_⟩
    change ((1 : ZMod 5) + c) * (((1 : ZMod 5) + c)⁻¹ * y) = y
    rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]


-- created on 2026-10-23
-- updated on 2026-10-28
