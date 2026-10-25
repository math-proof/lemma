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
import Theorem.v1.Atlas.TensorCategories.code.QuantumSl2Instance.Part3
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

/-- Assembles the candidate comultiplication, counit, and antipode together with the
structural axioms into a `SmallQuantumSl2HopfData` instance. -/
noncomputable instance instSmallQuantumSl2HopfData :
    SmallQuantumSl2HopfData n k q where
  comulHom := comulHomAux n k q
  counitHom := counitHomAux n k q
  antipodeLin := antipodeLinAux n k q
  comulHom_K := comulHomAux_K n k q
  comulHom_E := comulHomAux_E n k q
  comulHom_F := comulHomAux_F n k q
  counitHom_K := counitHomAux_K n k q
  counitHom_E := counitHomAux_E n k q
  counitHom_F := counitHomAux_F n k q
  antipodeLin_K := antipodeLinAux_K n k q
  antipodeLin_E := antipodeLinAux_E n k q
  antipodeLin_F := antipodeLinAux_F n k q
  coassoc_axiom := QuantumSl2StructuralAxioms.coassoc
  rTensor_counit_axiom := QuantumSl2StructuralAxioms.rTensor_counit
  lTensor_counit_axiom := QuantumSl2StructuralAxioms.lTensor_counit
  mul_antipode_rTensor_axiom :=
    QuantumSl2StructuralAxioms.hopf_right
      (antipodeLinAux n k q)
      (antipodeLinAux_K n k q)
      (antipodeLinAux_E n k q)
      (antipodeLinAux_F n k q)
  mul_antipode_lTensor_axiom :=
    QuantumSl2StructuralAxioms.hopf_left
      (antipodeLinAux n k q)
      (antipodeLinAux_K n k q)
      (antipodeLinAux_E n k q)
      (antipodeLinAux_F n k q)


end SmallQuantumSl2Instance
