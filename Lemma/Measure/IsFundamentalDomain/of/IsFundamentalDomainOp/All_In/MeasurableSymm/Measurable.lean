import Mathlib
import sympy.Basic

open MeasureTheory
open scoped Pointwise

/--
[MeasureTheory_IsFundamentalDomain_image_mulEquiv_op_subgroupOf](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_MeasureTheory_IsFundamentalDomain_image_mulEquiv_op_subgroupOf.lean)
-/
@[main]
private lemma main
  {A B : Type*} [Group A] [Group B] [MeasurableSpace A] [MeasurableSpace B] [MeasurableMul A] [MeasurableMul B]
  {H : Subgroup A}
  {H' : Subgroup B}
  {μ : Measure A}
  {D : Set A}
-- given
  (e : A ≃* B)
  (he : Measurable e)
  (he' : Measurable e.symm)
  (hH : ∀ a : A, e a ∈ H' ↔ a ∈ H)
  (hD : IsFundamentalDomain H.op D μ) :
-- imply
  IsFundamentalDomain H'.op (e '' D) (μ.map e) := by
-- proof
  classical

  have hmp : MeasurePreserving e.symm (μ.map e) μ := by
    refine ⟨he', ?_⟩
    rw [Measure.map_map he' he]
    have : (e.symm : B → A) ∘ (e : A → B) = id := funext fun a => e.symm_apply_apply a
    rw [this, Measure.map_id]

  let eg : H'.op ≃ H.op :=
    { toFun := fun h => ⟨MulOpposite.op (e.symm (MulOpposite.unop (h : Bᵐᵒᵖ))), by
        rw [Subgroup.mem_op, MulOpposite.unop_op, ← hH, MulEquiv.apply_symm_apply]
        exact Subgroup.mem_op.mp h.2⟩
      invFun := fun h => ⟨MulOpposite.op (e (MulOpposite.unop (h : Aᵐᵒᵖ))), by
        rw [Subgroup.mem_op, MulOpposite.unop_op, hH]
        exact Subgroup.mem_op.mp h.2⟩
      left_inv := fun h => by
        apply Subtype.ext
        simp only [MulOpposite.unop_op, MulEquiv.apply_symm_apply, MulOpposite.op_unop]
      right_inv := fun h => by
        apply Subtype.ext
        simp only [MulOpposite.unop_op, MulEquiv.symm_apply_apply, MulOpposite.op_unop] }
  refine hD.image_of_equiv e.toEquiv hmp.quasiMeasurePreserving eg fun g x => ?_

  show e ((eg g : Aᵐᵒᵖ) • x) = (g : Bᵐᵒᵖ) • e x
  rw [MulOpposite.smul_eq_mul_unop, MulOpposite.smul_eq_mul_unop, map_mul]
  congr 1
  exact e.apply_symm_apply _


-- created on 2026-10-05
