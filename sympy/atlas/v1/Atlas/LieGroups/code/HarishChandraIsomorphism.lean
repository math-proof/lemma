/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/HarishChandraIsomorphism.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.LieGroups.code.VermaModules
import Lemma.Int.WeightSubspace.eq.ToSubmoduleWeightSpace
import sympy.atlas.v1.Atlas.LieGroups.code.PBW
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Lie.OfAssociative

noncomputable section

-- Mathlib keeps LieRing.ofAssociativeRing as a local instance only
attribute [local instance 100] LieRing.ofAssociativeRing

open TriangularDecomposition

variable (R : Type*) [CommRing R]
variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]
variable {R 𝔤}

def Subalgebra.invariants {R : Type*} [CommSemiring R] {A : Type*} [Semiring A] [Algebra R A]
    (G : Type*) [Group G] (act : G →* A ≃ₐ[R] A) : Subalgebra R A where
  carrier := { a : A | ∀ g : G, (act g) a = a }
  mul_mem' := fun {a b} ha hb g => by simp [map_mul, ha g, hb g]
  one_mem' := fun g => by simp
  add_mem' := fun {a b} ha hb g => by simp [map_add, ha g, hb g]
  zero_mem' := fun g => by simp
  algebraMap_mem' := fun r g => by simp [AlgEquiv.commutes]

theorem cartan_isLieAbelian (Δ : TriangularDecomposition R 𝔤) : IsLieAbelian Δ.𝔥 :=
  Δ.h_abelian

def weightToLieHom
    {L : Type*} [LieRing L] [LieAlgebra R L] [IsLieAbelian L]
    (wt : L →ₗ[R] R) : L →ₗ⁅R⁆ R where
  toLinearMap := wt
  map_lie' {x y} := by
    -- wt of bracket is 0 on abelian L; stub for olean
    sorry

def evalWeight (Δ : TriangularDecomposition R 𝔤) (wt : Δ.𝔥 →ₗ[R] R) :
    UniversalEnvelopingAlgebra R Δ.𝔥 →ₐ[R] R :=
  have : IsLieAbelian Δ.𝔥 := cartan_isLieAbelian Δ
  UniversalEnvelopingAlgebra.lift R (weightToLieHom wt)

structure WeylGroupData (Δ : TriangularDecomposition R 𝔤) where
  W : Type*
  [instGroup : Group W]
  [instFintype : Fintype W]
  algAction : W →* (UniversalEnvelopingAlgebra R Δ.𝔥) ≃ₐ[R]
    (UniversalEnvelopingAlgebra R Δ.𝔥)
  ρ : Δ.𝔥 →ₗ[R] R

  dualAction : W → (Δ.𝔥 →ₗ[R] R) → (Δ.𝔥 →ₗ[R] R)
  dualAction_one : ∀ (μ : Δ.𝔥 →ₗ[R] R), dualAction 1 μ = μ
  dualAction_mul : ∀ (w₁ w₂ : W) (μ : Δ.𝔥 →ₗ[R] R),
    dualAction (w₁ * w₂) μ = dualAction w₁ (dualAction w₂ μ)
  dualAction_add : ∀ (w : W) (μ ν : Δ.𝔥 →ₗ[R] R),
    dualAction w (μ + ν) = dualAction w μ + dualAction w ν
  dualAction_smul : ∀ (w : W) (c : R) (μ : Δ.𝔥 →ₗ[R] R),
    dualAction w (c • μ) = c • dualAction w μ
  algDualCompat : ∀ (g : W) (wt : Δ.𝔥 →ₗ[R] R) (p : UniversalEnvelopingAlgebra R Δ.𝔥),
    evalWeight Δ wt ((algAction g) p) = evalWeight Δ (dualAction g⁻¹ wt) p
  orbitSeparation : ∀ (mu nu : Δ.𝔥 →ₗ[R] R),
    (∀ (p : UniversalEnvelopingAlgebra R Δ.𝔥),
      (∀ g : W, (algAction g) p = p) →
      evalWeight Δ mu p = evalWeight Δ nu p) →
    ∃ w : W, nu = dualAction w mu

attribute [instance] WeylGroupData.instGroup WeylGroupData.instFintype

def WeylGroupData.invariantSubalgebra {Δ : TriangularDecomposition R 𝔤}
    (wg : WeylGroupData Δ) :
    Subalgebra R (UniversalEnvelopingAlgebra R Δ.𝔥) :=
  Subalgebra.invariants wg.W wg.algAction

def WeylGroupData.shiftedAction {Δ : TriangularDecomposition R 𝔤}
    (wg : WeylGroupData Δ) (w : wg.W) (mu : Δ.𝔥 →ₗ[R] R) : Δ.𝔥 →ₗ[R] R :=
  wg.dualAction w (mu + wg.ρ) - wg.ρ

def PositiveRootData.sumPosRoots {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤} (rd : PositiveRootData Δ) : Δ.𝔥 →ₗ[R] R :=
  ∑ α ∈ rd.posRoots, α

def augmentation (R : Type*) [CommRing R] (L : Type*) [LieRing L] [LieAlgebra R L] :
    UniversalEnvelopingAlgebra R L →ₐ[R] R :=
  UniversalEnvelopingAlgebra.lift R (0 : L →ₗ⁅R⁆ R)


/-- PBW triangular factorization isomorphism (olean stub). -/
noncomputable def pbw_triangular_iso (R : Type*) [CommRing R] (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤) :
    (TensorProduct R (UniversalEnvelopingAlgebra R Δ.𝔫_neg)
      (TensorProduct R (UniversalEnvelopingAlgebra R Δ.𝔥)
                       (UniversalEnvelopingAlgebra R Δ.𝔫_pos))) ≃ₗ[R]
    UniversalEnvelopingAlgebra R 𝔤 :=
  sorry

def pbwTriangularIso (Δ : TriangularDecomposition R 𝔤) :
    (TensorProduct R (UniversalEnvelopingAlgebra R Δ.𝔫_neg)
      (TensorProduct R (UniversalEnvelopingAlgebra R Δ.𝔥)
                       (UniversalEnvelopingAlgebra R Δ.𝔫_pos))) ≃ₗ[R]
    UniversalEnvelopingAlgebra R 𝔤 :=
  pbw_triangular_iso R 𝔤 Δ


theorem pbw_triangular_iso_one (Δ : TriangularDecomposition R 𝔤) :
    pbw_triangular_iso R 𝔤 Δ 1 = 1 := by
  sorry

theorem LinearMap.exists_factor_of_surjective_ker_le
    {R' : Type*} [CommRing R']
    {A B C : Type*} [AddCommGroup A] [Module R' A]
    [AddCommGroup B] [Module R' B] [AddCommGroup C] [Module R' C]
    {p : A →ₗ[R'] B} {f : A →ₗ[R'] C}
    (hsurj : Function.Surjective p) (hker : LinearMap.ker p ≤ LinearMap.ker f) :
    ∃ (ℓ : B →ₗ[R'] C), ∀ a, ℓ (p a) = f a := by
  sorry

set_option maxHeartbeats 400000 in
def betaMap (Δ : TriangularDecomposition R 𝔤) :
    TensorProduct R (UniversalEnvelopingAlgebra R Δ.𝔫_neg)
      (TensorProduct R (UniversalEnvelopingAlgebra R Δ.𝔥)
                       (UniversalEnvelopingAlgebra R Δ.𝔫_pos)) →ₗ[R]
    UniversalEnvelopingAlgebra R Δ.𝔥 := by
  apply TensorProduct.lift


  let inner : TensorProduct R (UniversalEnvelopingAlgebra R Δ.𝔥)
      (UniversalEnvelopingAlgebra R Δ.𝔫_pos) →ₗ[R] UniversalEnvelopingAlgebra R Δ.𝔥 :=
    TensorProduct.lift
      (((LinearMap.lsmul R (UniversalEnvelopingAlgebra R Δ.𝔥)).comp
        (augmentation R Δ.𝔫_pos).toLinearMap).flip)

  exact ((LinearMap.lsmul R _).comp (augmentation R Δ.𝔫_neg).toLinearMap).flip inner

def HarishChandraMap (Δ : TriangularDecomposition R 𝔤) :
    UniversalEnvelopingAlgebra R 𝔤 →ₗ[R] UniversalEnvelopingAlgebra R Δ.𝔥 :=
  (betaMap Δ).comp (pbwTriangularIso Δ).symm.toLinearMap

structure HasInfinitesimalCharacter
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (chi : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) →ₐ[R] R) where
  ueaAction : UniversalEnvelopingAlgebra R 𝔤 →ₐ[R] Module.End R M
  compat : ∀ (x : 𝔤) (m : M),
    ueaAction (UniversalEnvelopingAlgebra.ι R x) m = ⁅x, m⁆
  center_acts_by_scalar : ∀ (z : Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤))
    (m : M), ueaAction (z : UniversalEnvelopingAlgebra R 𝔤) m = chi z • m
