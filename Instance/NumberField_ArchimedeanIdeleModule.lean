-- Carved from Lemma/Definitions/Def_NumberField_ArchimedeanIdeleModule.lean: instance decls only.
import Mathlib
import Lemma.GroupCohomology.RepPi
import Abbrev.NumberField_ArchimedeanIdeleModule

set_option autoImplicit false

open NumberField

namespace NumberField.InfPlaceDecomp


variable (E K : Type*) [Field E] [Field K] [Algebra E K] (w : InfinitePlace K)


noncomputable scoped instance instMulActionWithAbs : MulAction (decomp E K w) (WithAbs w.1) where
  one_smul y := by rw [smul_withAbs_def]; rfl
  mul_smul σ τ y := by rw [smul_withAbs_def, smul_withAbs_def, smul_withAbs_def]; rfl

noncomputable scoped instance instDistribMulActionWithAbs : DistribMulAction (decomp E K w) (WithAbs w.1) where
  smul_zero σ := by rw [smul_withAbs_def]; show WithAbs.toAbs _ ((σ : K ≃ₐ[E] K) 0) = 0; rw [map_zero]; rfl
  smul_add σ x y := by
    rw [smul_withAbs_def, smul_withAbs_def, smul_withAbs_def]
    show WithAbs.toAbs _ ((σ : K ≃ₐ[E] K) (x.ofAbs + y.ofAbs)) = _
    rw [map_add]; rfl

noncomputable scoped instance instUniformContinuousConstSMul : UniformContinuousConstSMul (decomp E K w) (WithAbs w.1) :=
  ⟨fun σ => uniformContinuous_congr_of_mem (σ : K ≃ₐ[E] K) σ.2⟩

noncomputable scoped instance instMulSemiringAction : MulSemiringAction (decomp E K w) w.Completion where
  smul σ x := actRingEquiv σ x
  one_smul x := by change actRingEquiv 1 x = x; rw [actRingEquiv_one]; rfl
  mul_smul σ τ x := by
    change actRingEquiv (σ * τ) x = actRingEquiv σ (actRingEquiv τ x); rw [actRingEquiv_mul]; rfl
  smul_zero σ := by change actRingEquiv σ 0 = 0; rw [map_zero]
  smul_add σ x y := by change actRingEquiv σ (x + y) = actRingEquiv σ x + actRingEquiv σ y; rw [map_add]
  smul_one σ := by change actRingEquiv σ 1 = 1; rw [map_one]
  smul_mul σ x y := by change actRingEquiv σ (x * y) = actRingEquiv σ x * actRingEquiv σ y; rw [map_mul]

scoped instance instContinuousConstSMul : ContinuousConstSMul (decomp E K w) w.Completion :=
  ⟨fun σ => continuous_actRingEquiv σ⟩

noncomputable scoped instance instMulDistribMulActionUnits : MulDistribMulAction (decomp E K w) (w.Completion)ˣ :=
  Units.mulDistribMulActionRight

noncomputable scoped instance instMulActionUnits : MulAction (decomp E K w) (w.Completion)ˣ :=
  (instMulDistribMulActionUnits (E := E) (K := K) (w := w)).toMulAction

noncomputable scoped instance instSMulUnits : SMul (decomp E K w) (w.Completion)ˣ :=
  (instMulActionUnits (E := E) (K := K) (w := w)).toSMul

variable (E K w) in


end NumberField.InfPlaceDecomp

