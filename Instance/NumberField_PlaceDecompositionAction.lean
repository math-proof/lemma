-- Carved from Lemma/Definitions/Def_NumberField_PlaceDecompositionAction.lean: instance decls only.
import Mathlib
import Lemma.NumberField.PlaceDecompositionAction

set_option autoImplicit false

open IsDedekindDomain NumberField
open scoped Pointwise

namespace NumberField.PlaceDecomp


variable (E K : Type*) [Field E] [Field K] [NumberField K] [Algebra E K] (w : HeightOneSpectrum (𝓞 K))

variable {E K w}

noncomputable scoped instance instMulActionWithVal : MulAction (decomp E K w) (WithVal (w.valuation K)) where
  one_smul y := by rw [smul_withVal_def]; rfl
  mul_smul σ τ y := by rw [smul_withVal_def, smul_withVal_def, smul_withVal_def]; rfl

noncomputable scoped instance instDistribMulActionWithVal : DistribMulAction (decomp E K w) (WithVal (w.valuation K)) where
  smul_zero σ := by rw [smul_withVal_def]; show WithVal.toVal _ ((σ : K ≃ₐ[E] K) 0) = 0; rw [map_zero]; rfl
  smul_add σ x y := by
    rw [smul_withVal_def, smul_withVal_def, smul_withVal_def]
    show WithVal.toVal _ ((σ : K ≃ₐ[E] K) (x.ofVal + y.ofVal)) = _
    rw [map_add]; rfl

noncomputable scoped instance instUniformContinuousConstSMul :
    UniformContinuousConstSMul (decomp E K w) (WithVal (w.valuation K)) :=
  ⟨fun σ => uniformContinuous_congr_of_mem (σ : K ≃ₐ[E] K) σ.2⟩

noncomputable scoped instance instMulSemiringAction : MulSemiringAction (decomp E K w) (w.adicCompletion K) where
  smul σ x := actRingEquiv σ x
  one_smul x := by change actRingEquiv 1 x = x; rw [actRingEquiv_one]; rfl
  mul_smul σ τ x := by change actRingEquiv (σ * τ) x = actRingEquiv σ (actRingEquiv τ x); rw [actRingEquiv_mul]; rfl
  smul_zero σ := by change actRingEquiv σ 0 = 0; rw [map_zero]
  smul_add σ x y := by change actRingEquiv σ (x + y) = actRingEquiv σ x + actRingEquiv σ y; rw [map_add]
  smul_one σ := by change actRingEquiv σ 1 = 1; rw [map_one]
  smul_mul σ x y := by change actRingEquiv σ (x * y) = actRingEquiv σ x * actRingEquiv σ y; rw [map_mul]

noncomputable scoped instance instMulDistribMulActionUnits : MulDistribMulAction (decomp E K w) (w.adicCompletion K)ˣ :=
  Units.mulDistribMulActionRight

section integers

noncomputable scoped instance instSMulIntegers : SMul (decomp E K w) (w.adicCompletionIntegers K) :=
  ⟨fun σ x => ⟨σ • (x : w.adicCompletion K), (smul_mem_adicCompletionIntegers_iff σ _).2 x.2⟩⟩

set_option synthInstance.maxHeartbeats 200000 in

noncomputable scoped instance instMulSemiringActionIntegers : MulSemiringAction (decomp E K w) (w.adicCompletionIntegers K) :=
  { instSMulIntegers (E := E) (K := K) (w := w) with
    one_smul := fun x => Subtype.ext (by rw [coe_smul_integers, one_smul])
    mul_smul := fun σ τ x => Subtype.ext (by rw [coe_smul_integers, coe_smul_integers, coe_smul_integers, mul_smul])
    smul_zero := fun σ => Subtype.ext (by rw [coe_smul_integers]; exact smul_zero σ)
    smul_add := fun σ x y => Subtype.ext (by rw [coe_smul_integers]; exact smul_add σ (x : w.adicCompletion K) y)
    smul_one := fun σ => Subtype.ext (by rw [coe_smul_integers]; exact smul_one σ)
    smul_mul := fun σ x y => Subtype.ext (by rw [coe_smul_integers]; exact MulSemiringAction.smul_mul σ (x : w.adicCompletion K) y) }

set_option synthInstance.maxHeartbeats 200000 in

noncomputable scoped instance instMulDistribMulActionIntegerUnits : MulDistribMulAction (decomp E K w) (w.adicCompletionIntegers K)ˣ :=
  Units.mulDistribMulActionRight

noncomputable scoped instance instMulActionIntegers : MulAction (decomp E K w) (w.adicCompletionIntegers K) :=
  (instMulSemiringActionIntegers (E := E) (K := K) (w := w)).toMulAction

set_option synthInstance.maxHeartbeats 200000 in
noncomputable scoped instance instSMulUnits : SMul (decomp E K w) (w.adicCompletion K)ˣ :=
  (instMulDistribMulActionUnits (E := E) (K := K) (w := w)).toMulAction.toSMul

set_option synthInstance.maxHeartbeats 200000 in
noncomputable scoped instance instSMulIntegerUnits : SMul (decomp E K w) (w.adicCompletionIntegers K)ˣ :=
  (instMulDistribMulActionIntegerUnits (E := E) (K := K) (w := w)).toMulAction.toSMul

set_option synthInstance.maxHeartbeats 200000 in
noncomputable scoped instance instMulActionUnits : MulAction (decomp E K w) (w.adicCompletion K)ˣ :=
  (instMulDistribMulActionUnits (E := E) (K := K) (w := w)).toMulAction

set_option synthInstance.maxHeartbeats 200000 in
noncomputable scoped instance instMulActionIntegerUnits : MulAction (decomp E K w) (w.adicCompletionIntegers K)ˣ :=
  (instMulDistribMulActionIntegerUnits (E := E) (K := K) (w := w)).toMulAction

end integers

end NumberField.PlaceDecomp
