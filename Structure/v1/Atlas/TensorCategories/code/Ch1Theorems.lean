/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Ch1Theorems.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Free.Coherence
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.Skeleton
import Mathlib.CategoryTheory.Skeletal
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Abelian.Projective.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.RingTheory.HopfAlgebra.Basic
import Def.v1.Atlas.TensorCategories.code.SemisimpleMultitensor.Part6
import Lemma.Category.Atlas.v1.TensorCategories.code.SemisimpleMultitensor
import Lemma.Category.Atlas.v1.TensorCategories.code.QuasiTensorFunctorProjective
import Theorem.v1.Atlas.TensorCategories.code.UnitSemisimplicity
import Class.v1.Atlas.TensorCategories.code.QuasiTensorFunctorProjective.Part3
set_option maxHeartbeats 400000

open CategoryTheory MonoidalCategory Limits

universe u v w u₁ v₁


/-- A monoidal category `C` is strict (Definition 1.8.1) if the tensor product is strictly
associative and strictly unital, i.e., `(X ⊗ Y) ⊗ Z = X ⊗ (Y ⊗ Z)`, `𝟙_ C ⊗ X = X` and
`X ⊗ 𝟙_ C = X` hold on the nose. -/
structure IsStrictMonoidal (C : Type*) [Category C] [MonoidalCategory C] : Prop where
  tensorObj_assoc : ∀ (X Y Z : C), (X ⊗ Y) ⊗ Z = X ⊗ (Y ⊗ Z)
  tensorUnit_left : ∀ (X : C), 𝟙_ C ⊗ X = X
  tensorUnit_right : ∀ (X : C), X ⊗ 𝟙_ C = X


open scoped TensorProduct in
/-- Definition 1.25.1 / Theorem 1.25.2: A witness for the Hopf algebra `U_q(sl_2)`. It
packages the carrier algebra `H` with generators `K`, `K⁻¹`, `E`, `F` satisfying the
defining commutation relations and the prescribed comultiplication. -/
structure QuantumSl2Witness (k : Type u) [Field k] (q : k) where
  carrier : Type u
  instRing : Ring carrier
  instHopf : @HopfAlgebra k carrier _ instRing.toSemiring
  K : carrier
  Kinv : carrier
  E : carrier
  F : carrier
  K_mul_Kinv : letI := instRing; K * Kinv = 1
  Kinv_mul_K : letI := instRing; Kinv * K = 1
  K_E_Kinv : letI := instRing; letI := instHopf.toAlgebra; K * E * Kinv = q ^ 2 • E
  K_F_Kinv : letI := instRing; letI := instHopf.toAlgebra; K * F * Kinv = (q ^ 2)⁻¹ • F
  EF_comm : letI := instRing; letI := instHopf.toAlgebra;
    E * F - F * E = (q - q⁻¹)⁻¹ • (K - Kinv)
  comul_K : letI := instRing.toSemiring; letI := instHopf;
    Coalgebra.comul (R := k) K = K ⊗ₜ[k] K
  comul_E : letI := instRing.toSemiring; letI := instHopf;
    Coalgebra.comul (R := k) E = E ⊗ₜ[k] K + 1 ⊗ₜ[k] E
  comul_F : letI := instRing.toSemiring; letI := instHopf;
    Coalgebra.comul (R := k) F = F ⊗ₜ[k] 1 + Kinv ⊗ₜ[k] F

