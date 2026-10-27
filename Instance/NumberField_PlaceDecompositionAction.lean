-- Carved from Lemma/Definitions/Def_NumberField_PlaceDecompositionAction.lean: instance decls only.
import Mathlib
import Lemma.NumberField.PlaceDecompositionAction

set_option autoImplicit false

open IsDedekindDomain NumberField
open scoped Pointwise

namespace NumberField.PlaceDecomp


variable (E K : Type*) [Field E] [Field K] [NumberField K] [Algebra E K] (w : HeightOneSpectrum (𝓞 K))

variable {E K w}

section integers

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
