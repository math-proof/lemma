/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumSl2Instance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Instance.v1.Atlas.TensorCategories.code.QuantumSl2Concrete.Part5
import Lemma.Category.Atlas.v1.TensorCategories.code.QuantumSl2Concrete
import Lemma.Category.Atlas.v1.TensorCategories.code.QBinomial
import Theorem.v1.Atlas.TensorCategories.code.QBinomial.Part2
import Def.v1.Atlas.TensorCategories.code.QuantumSl2Instance.Part3
open Coalgebra HopfAlgebra
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 800000


namespace SmallQuantumSl2Instance

variable (n : ℕ) (k : Type*) [Field k] (q : k)

local notation "A" => SmallQuantumSl2Alg n k q

local notation "KK" => SmallQuantumSl2Alg.K n k q

local notation "EE" => SmallQuantumSl2Alg.E n k q

local notation "FF" => SmallQuantumSl2Alg.F n k q

local notation "Kinv" => SmallQuantumSl2Alg.Kinv n k q

variable [hyp : QuantumSl2Hypotheses n k q]

include hyp

variable [QuantumSl2StructuralAxioms n k q]

/-- The antipode satisfies `S(K) = K^{-1}`. -/
lemma antipodeLinAux_K :
    antipodeLinAux n k q KK = Kinv :=
  (QuantumSl2StructuralAxioms.antipode_exists
    (n := n) (k := k) (q := q)).choose_spec.1

/-- The antipode satisfies `S(E) = -E · K^{-1}`. -/
lemma antipodeLinAux_E :
    antipodeLinAux n k q EE = -(EE * Kinv) :=
  (QuantumSl2StructuralAxioms.antipode_exists
    (n := n) (k := k) (q := q)).choose_spec.2.1

/-- The antipode satisfies `S(F) = -K · F`. -/
lemma antipodeLinAux_F :
    antipodeLinAux n k q FF = -(KK * FF) :=
  (QuantumSl2StructuralAxioms.antipode_exists
    (n := n) (k := k) (q := q)).choose_spec.2.2

omit [QuantumSl2StructuralAxioms n k q] in
/-- `comulHomAux(K) = K ⊗ K`. -/
lemma comulHomAux_K :
    comulHomAux n k q KK = KK ⊗ₜ[k] KK := by
  unfold comulHomAux SmallQuantumSl2Alg.K SmallQuantumSl2Alg.lift SmallQuantumSl2Alg.π DeltaK
  erw [RingQuot.liftAlgHom_mkAlgHom_apply, FreeAlgebra.lift_ι_apply]
  dsimp only []
  rfl

omit [QuantumSl2StructuralAxioms n k q] in
/-- `comulHomAux(E) = E ⊗ K + 1 ⊗ E`. -/
lemma comulHomAux_E :
    comulHomAux n k q EE = EE ⊗ₜ[k] KK + 1 ⊗ₜ[k] EE := by
  unfold comulHomAux SmallQuantumSl2Alg.E SmallQuantumSl2Alg.K SmallQuantumSl2Alg.lift
    SmallQuantumSl2Alg.π DeltaE
  erw [RingQuot.liftAlgHom_mkAlgHom_apply, FreeAlgebra.lift_ι_apply]
  dsimp only []
  rfl

omit [QuantumSl2StructuralAxioms n k q] in
/-- `comulHomAux(F) = F ⊗ 1 + K^{-1} ⊗ F`. -/
lemma comulHomAux_F :
    comulHomAux n k q FF = FF ⊗ₜ[k] 1 + Kinv ⊗ₜ[k] FF := by
  unfold comulHomAux SmallQuantumSl2Alg.F SmallQuantumSl2Alg.Kinv SmallQuantumSl2Alg.lift
    SmallQuantumSl2Alg.π DeltaF
  erw [RingQuot.liftAlgHom_mkAlgHom_apply, FreeAlgebra.lift_ι_apply]
  dsimp only []
  rfl

omit [QuantumSl2StructuralAxioms n k q] in
/-- `counitHomAux(K) = 1`. -/
lemma counitHomAux_K :
    counitHomAux n k q KK = 1 := by
  unfold counitHomAux SmallQuantumSl2Alg.K SmallQuantumSl2Alg.lift SmallQuantumSl2Alg.π
  erw [RingQuot.liftAlgHom_mkAlgHom_apply, FreeAlgebra.lift_ι_apply]

omit [QuantumSl2StructuralAxioms n k q] in
/-- `counitHomAux(E) = 0`. -/
lemma counitHomAux_E :
    counitHomAux n k q EE = 0 := by
  unfold counitHomAux SmallQuantumSl2Alg.E SmallQuantumSl2Alg.lift SmallQuantumSl2Alg.π
  erw [RingQuot.liftAlgHom_mkAlgHom_apply, FreeAlgebra.lift_ι_apply]

omit [QuantumSl2StructuralAxioms n k q] in
/-- `counitHomAux(F) = 0`. -/
lemma counitHomAux_F :
    counitHomAux n k q FF = 0 := by
  unfold counitHomAux SmallQuantumSl2Alg.F SmallQuantumSl2Alg.lift SmallQuantumSl2Alg.π
  erw [RingQuot.liftAlgHom_mkAlgHom_apply, FreeAlgebra.lift_ι_apply]

end SmallQuantumSl2Instance
