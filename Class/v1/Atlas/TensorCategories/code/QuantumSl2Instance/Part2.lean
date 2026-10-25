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
import Def.v1.Atlas.TensorCategories.code.QuantumSl2Instance.Part2
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

/-- Auxiliary structural axioms packaging the existence of an antipode and the
coassociativity / counitality / Hopf-algebra axioms for the candidate `comulHomAux`,
`counitHomAux` on the small quantum group. -/
class QuantumSl2StructuralAxioms (n : ℕ) (k : Type*) [Field k] (q : k)
    [QuantumSl2Hypotheses n k q] : Prop where
  antipode_exists :
    ∃ (S : SmallQuantumSl2Alg n k q →ₗ[k] SmallQuantumSl2Alg n k q),
      S (SmallQuantumSl2Alg.K n k q) = SmallQuantumSl2Alg.Kinv n k q ∧
      S (SmallQuantumSl2Alg.E n k q) =
        -(SmallQuantumSl2Alg.E n k q * SmallQuantumSl2Alg.Kinv n k q) ∧
      S (SmallQuantumSl2Alg.F n k q) =
        -(SmallQuantumSl2Alg.K n k q * SmallQuantumSl2Alg.F n k q)
  coassoc :
    (Algebra.TensorProduct.assoc k k k
      (SmallQuantumSl2Alg n k q) (SmallQuantumSl2Alg n k q)
      (SmallQuantumSl2Alg n k q)).toAlgHom.comp
      ((Algebra.TensorProduct.map (comulHomAux n k q) (AlgHom.id k _)).comp
        (comulHomAux n k q)) =
    (Algebra.TensorProduct.map (AlgHom.id k _) (comulHomAux n k q)).comp
      (comulHomAux n k q)
  rTensor_counit :
    (Algebra.TensorProduct.map (counitHomAux n k q) (AlgHom.id k _)).comp
      (comulHomAux n k q) =
    (Algebra.TensorProduct.lid k (SmallQuantumSl2Alg n k q)).symm.toAlgHom
  lTensor_counit :
    (Algebra.TensorProduct.map (AlgHom.id k _) (counitHomAux n k q)).comp
      (comulHomAux n k q) =
    (Algebra.TensorProduct.rid k k (SmallQuantumSl2Alg n k q)).symm.toAlgHom
  hopf_right :
    ∀ (S : SmallQuantumSl2Alg n k q →ₗ[k] SmallQuantumSl2Alg n k q),
      S (SmallQuantumSl2Alg.K n k q) = SmallQuantumSl2Alg.Kinv n k q →
      S (SmallQuantumSl2Alg.E n k q) =
        -(SmallQuantumSl2Alg.E n k q * SmallQuantumSl2Alg.Kinv n k q) →
      S (SmallQuantumSl2Alg.F n k q) =
        -(SmallQuantumSl2Alg.K n k q * SmallQuantumSl2Alg.F n k q) →
      LinearMap.mul' k (SmallQuantumSl2Alg n k q) ∘ₗ
        LinearMap.rTensor _ S ∘ₗ (comulHomAux n k q).toLinearMap =
      Algebra.linearMap k _ ∘ₗ (counitHomAux n k q).toLinearMap
  hopf_left :
    ∀ (S : SmallQuantumSl2Alg n k q →ₗ[k] SmallQuantumSl2Alg n k q),
      S (SmallQuantumSl2Alg.K n k q) = SmallQuantumSl2Alg.Kinv n k q →
      S (SmallQuantumSl2Alg.E n k q) =
        -(SmallQuantumSl2Alg.E n k q * SmallQuantumSl2Alg.Kinv n k q) →
      S (SmallQuantumSl2Alg.F n k q) =
        -(SmallQuantumSl2Alg.K n k q * SmallQuantumSl2Alg.F n k q) →
      LinearMap.mul' k (SmallQuantumSl2Alg n k q) ∘ₗ
        LinearMap.lTensor _ S ∘ₗ (comulHomAux n k q).toLinearMap =
      Algebra.linearMap k _ ∘ₗ (counitHomAux n k q).toLinearMap

end SmallQuantumSl2Instance
