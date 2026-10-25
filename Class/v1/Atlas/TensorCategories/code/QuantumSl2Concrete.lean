/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumSl2Concrete.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.Algebra.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.RingQuot
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Def.v1.Atlas.TensorCategories.code.QuantumSl2.Part2
import Lemma.Category.Atlas.v1.TensorCategories.code.QuantumSl2
import Def.v1.Atlas.TensorCategories.code.QuantumSl2Concrete.Part4
variable {n : ℕ} {k : Type*} [Field k]


namespace SmallQuantumSl2

variable (n : ℕ) (k : Type*) [Field k] (q : k)

open Coalgebra HopfAlgebra

open scoped TensorProduct

set_option synthInstance.maxHeartbeats 800000

/-- A bundle of data witnessing that `SmallQuantumSl2Alg n k q` carries a
bialgebra/Hopf-algebra structure with prescribed values of the comultiplication,
counit, and antipode on the generators `K, E, F`, together with the coherence axioms. -/
class SmallQuantumSl2HopfData (n : ℕ) (k : Type*) [Field k] (q : k) where
  comulHom : SmallQuantumSl2Alg n k q →ₐ[k]
    SmallQuantumSl2Alg n k q ⊗[k] SmallQuantumSl2Alg n k q
  counitHom : SmallQuantumSl2Alg n k q →ₐ[k] k
  antipodeLin : SmallQuantumSl2Alg n k q →ₗ[k] SmallQuantumSl2Alg n k q
  comulHom_K : comulHom (SmallQuantumSl2Alg.K n k q) =
    SmallQuantumSl2Alg.K n k q ⊗ₜ[k] SmallQuantumSl2Alg.K n k q
  comulHom_E : comulHom (SmallQuantumSl2Alg.E n k q) =
    SmallQuantumSl2Alg.E n k q ⊗ₜ[k] SmallQuantumSl2Alg.K n k q +
    1 ⊗ₜ[k] SmallQuantumSl2Alg.E n k q
  comulHom_F : comulHom (SmallQuantumSl2Alg.F n k q) =
    SmallQuantumSl2Alg.F n k q ⊗ₜ[k] 1 +
    SmallQuantumSl2Alg.Kinv n k q ⊗ₜ[k] SmallQuantumSl2Alg.F n k q
  counitHom_K : counitHom (SmallQuantumSl2Alg.K n k q) = 1
  counitHom_E : counitHom (SmallQuantumSl2Alg.E n k q) = 0
  counitHom_F : counitHom (SmallQuantumSl2Alg.F n k q) = 0
  antipodeLin_K : antipodeLin (SmallQuantumSl2Alg.K n k q) =
    SmallQuantumSl2Alg.Kinv n k q
  antipodeLin_E : antipodeLin (SmallQuantumSl2Alg.E n k q) =
    -(SmallQuantumSl2Alg.E n k q * SmallQuantumSl2Alg.Kinv n k q)
  antipodeLin_F : antipodeLin (SmallQuantumSl2Alg.F n k q) =
    -(SmallQuantumSl2Alg.K n k q * SmallQuantumSl2Alg.F n k q)
  coassoc_axiom :
    (Algebra.TensorProduct.assoc k k k
      (SmallQuantumSl2Alg n k q) (SmallQuantumSl2Alg n k q)
      (SmallQuantumSl2Alg n k q)).toAlgHom.comp
      ((Algebra.TensorProduct.map comulHom (AlgHom.id k _)).comp comulHom) =
    (Algebra.TensorProduct.map (AlgHom.id k _) comulHom).comp comulHom
  rTensor_counit_axiom :
    (Algebra.TensorProduct.map counitHom (AlgHom.id k _)).comp comulHom =
    (Algebra.TensorProduct.lid k (SmallQuantumSl2Alg n k q)).symm.toAlgHom
  lTensor_counit_axiom :
    (Algebra.TensorProduct.map (AlgHom.id k _) counitHom).comp comulHom =
    (Algebra.TensorProduct.rid k k (SmallQuantumSl2Alg n k q)).symm.toAlgHom
  mul_antipode_rTensor_axiom : LinearMap.mul' k (SmallQuantumSl2Alg n k q) ∘ₗ
    LinearMap.rTensor _ antipodeLin ∘ₗ comulHom.toLinearMap =
    Algebra.linearMap k _ ∘ₗ counitHom.toLinearMap
  mul_antipode_lTensor_axiom : LinearMap.mul' k (SmallQuantumSl2Alg n k q) ∘ₗ
    LinearMap.lTensor _ antipodeLin ∘ₗ comulHom.toLinearMap =
    Algebra.linearMap k _ ∘ₗ counitHom.toLinearMap

end SmallQuantumSl2
