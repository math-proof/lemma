/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/VermaModules.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Algebra.Lie.Submodule
import Mathlib.Algebra.Lie.Quotient
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.Algebra.Lie.Weights.Basic
import Mathlib.Algebra.Lie.Semisimple.Basic
import Mathlib.Algebra.Lie.CartanSubalgebra
import Mathlib.Order.Atoms
import Mathlib.RingTheory.Congruence.Defs

noncomputable section

universe u_mod

variable (R : Type*) [CommRing R]
variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]

structure TriangularDecomposition where
  𝔥 : LieSubalgebra R 𝔤
  𝔫_pos : LieSubalgebra R 𝔤
  𝔫_neg : LieSubalgebra R 𝔤
  is_cartan : 𝔥.IsCartanSubalgebra
  h_abelian : IsLieAbelian 𝔥
  decomp_exists : ∀ x : 𝔤, ∃ (n_neg : 𝔫_neg) (h : 𝔥) (n_pos : 𝔫_pos),
    x = (n_neg : 𝔤) + (h : 𝔤) + (n_pos : 𝔤)
  decomp_unique : ∀ (n₁ n₁' : 𝔫_neg) (h₁ h₁' : 𝔥) (p₁ p₁' : 𝔫_pos),
    (n₁ : 𝔤) + (h₁ : 𝔤) + (p₁ : 𝔤) = (n₁' : 𝔤) + (h₁' : 𝔤) + (p₁' : 𝔤) →
    n₁ = n₁' ∧ h₁ = h₁' ∧ p₁ = p₁'

variable {R 𝔤}

namespace TriangularDecomposition

variable (Δ : TriangularDecomposition R 𝔤)

def 𝔟 : LieSubalgebra R 𝔤 := Δ.𝔥 ⊔ Δ.𝔫_pos

def weightSubspace
    (M : Type u_mod) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (μ : Δ.𝔥 →ₗ[R] R) : Submodule R M where
  carrier := {m : M | ∀ h : Δ.𝔥, ⁅(h : 𝔤), m⁆ = μ h • m}
  add_mem' {a b} ha hb h := by rw [lie_add, ha h, hb h, smul_add]
  zero_mem' h := by rw [lie_zero, smul_zero]
  smul_mem' c _ hm h := by rw [LieModule.lie_smul, hm h, smul_comm]

structure IsHighestWeightModule
    (Δ : TriangularDecomposition R 𝔤)
    (M : Type u_mod) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (wt : Δ.𝔥 →ₗ[R] R) where
  highestWeightVec : M
  hwv_ne_zero : highestWeightVec ≠ 0
  cartan_action : ∀ (h : Δ.𝔥), ⁅(h : 𝔤), highestWeightVec⁆ = wt h • highestWeightVec
  npos_action : ∀ (e : Δ.𝔫_pos), ⁅(e : 𝔤), highestWeightVec⁆ = 0
  generates : LieSubmodule.lieSpan R 𝔤 {highestWeightVec} = ⊤

structure IsVermaModule
    (Δ : TriangularDecomposition R 𝔤)
    (M : Type u_mod) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (wt : Δ.𝔥 →ₗ[R] R)
    extends IsHighestWeightModule Δ M wt where
  universal_map :
    ∀ (V : Type u_mod) [AddCommGroup V] [Module R V] [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
      (v : V),
      (∀ (h : Δ.𝔥), ⁅(h : 𝔤), v⁆ = wt h • v) →
      (∀ (e : Δ.𝔫_pos), ⁅(e : 𝔤), v⁆ = 0) →
      ∃ (η : M →ₗ⁅R, 𝔤⁆ V), η highestWeightVec = v
  universal_unique :
    ∀ (V : Type u_mod) [AddCommGroup V] [Module R V] [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
      (η₁ η₂ : M →ₗ⁅R, 𝔤⁆ V),
      η₁ highestWeightVec = η₂ highestWeightVec → η₁ = η₂

def ueaSubalgAction (𝔫 : LieSubalgebra R 𝔤)
    (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M] :
    UniversalEnvelopingAlgebra R (↥𝔫) →ₐ[R] Module.End R M :=
  UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R (↥𝔫) M)

def instModuleUEASubalg (𝔫 : LieSubalgebra R 𝔤)
    (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M] :
    Module (UniversalEnvelopingAlgebra R (↥𝔫)) M :=
  Module.compHom M (ueaSubalgAction 𝔫 M).toRingHom


section UEASubalgHelpers

variable {R : Type*} [CommRing R]
  {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {M : Type*} [AddCommGroup M] [Module R M]
  [LieRingModule 𝔤 M] [LieModule R 𝔤 M]

def augmentationUEA (R : Type*) [CommRing R] (L : Type*) [LieRing L] [LieAlgebra R L] :
    UniversalEnvelopingAlgebra R L →ₐ[R] R :=
  letI : LieRing R := LieRing.ofAssociativeRing
  letI : LieAlgebra R R := LieAlgebra.ofAssociativeAlgebra
  UniversalEnvelopingAlgebra.lift R (0 : L →ₗ⁅R⁆ R)

theorem IsVermaModule.quotient_by_maximal_irreducible (_hM : IsVermaModule Δ M wt)
    (J : LieSubmodule R 𝔤 M) (hJ_ne_top : J ≠ ⊤)
    (hJ_max : ∀ (N : LieSubmodule R 𝔤 M), N ≠ ⊤ → N ≤ J) :
    LieModule.IsIrreducible R 𝔤 (M ⧸ J) := by

  show IsSimpleOrder (LieSubmodule R 𝔤 (M ⧸ J))

  have : Nontrivial (LieSubmodule R 𝔤 (M ⧸ J)) := by
    refine ⟨⟨⊥, ⊤, ?_⟩⟩
    intro h
    apply hJ_ne_top
    rw [eq_top_iff]
    intro m _
    have hmem : (LieSubmodule.Quotient.mk' J) m ∈ (⊤ : LieSubmodule R 𝔤 (M ⧸ J)) := trivial
    rw [← h] at hmem
    rw [LieSubmodule.mem_bot] at hmem
    rwa [LieSubmodule.Quotient.mk_eq_zero] at hmem

  exact {
    eq_bot_or_eq_top := by
      intro N'

      set N := N'.comap (LieSubmodule.Quotient.mk' J) with hN_def

      have hJN : J ≤ N := by
        intro m hm
        show m ∈ N'.comap (LieSubmodule.Quotient.mk' J)
        rw [LieSubmodule.mem_comap]
        rw [(LieSubmodule.Quotient.mk_eq_zero J).mpr hm]
        exact N'.zero_mem

      by_cases hN : N = ⊤
      ·
        right; rw [eq_top_iff]; intro x _
        obtain ⟨m, rfl⟩ := LieSubmodule.Quotient.surjective_mk' J x
        exact (hN ▸ trivial : m ∈ N)
      ·
        left
        have hNJ : N ≤ J := hJ_max N hN
        rw [eq_bot_iff]; intro x hx
        obtain ⟨m, rfl⟩ := LieSubmodule.Quotient.surjective_mk' J x
        rw [LieSubmodule.mem_bot]
        exact (LieSubmodule.Quotient.mk_eq_zero J).mpr (hNJ hx) }

def WeightSpace (Δ : TriangularDecomposition R 𝔤)
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (μ : Δ.𝔥 →ₗ[R] R) : Submodule R M where
  carrier := { m : M | ∀ (h : Δ.𝔥), ⁅(h : 𝔤), m⁆ = μ h • m }
  add_mem' := fun {a b} ha hb h => by rw [lie_add, ha h, hb h, smul_add]
  zero_mem' := fun h => by rw [lie_zero, smul_zero]
  smul_mem' := fun r {m} hm h => by rw [lie_smul, hm h, smul_comm]

def weights (Δ : TriangularDecomposition R 𝔤)
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M] : Set (Δ.𝔥 →ₗ[R] R) :=
  { μ | WeightSpace Δ M μ ≠ ⊥ }

structure PositiveRootData (Δ : TriangularDecomposition R 𝔤) where
  posRoots : Finset (Δ.𝔥 →ₗ[R] R)
  posRoots_ne_zero : ∀ α ∈ posRoots, α ≠ 0
  posRoots_pointed_cone : ∀ (α : Δ.𝔥 →ₗ[R] R), α ∈ posRoots →
    ∀ (n : ℤ), n < 0 →
    ¬ ∃ (c : (Δ.𝔥 →ₗ[R] R) → ℕ), n • α = ∑ β ∈ posRoots, (c β) • β
  corootPairing : (Δ.𝔥 →ₗ[R] R) → (Δ.𝔥 →ₗ[R] R) → R
  corootPairing_add_left : ∀ (μ ν α : Δ.𝔥 →ₗ[R] R),
    corootPairing (μ + ν) α = corootPairing μ α + corootPairing ν α
  corootPairing_nsmul_left : ∀ (n : ℕ) (μ α : Δ.𝔥 →ₗ[R] R),
    corootPairing (n • μ) α = n • corootPairing μ α
  corootPairing_self : ∀ α ∈ posRoots, corootPairing α α = 2
  negRootVec : ∀ α ∈ posRoots, ↥(Δ.𝔫_neg)
  negRootVec_weight : ∀ (α : Δ.𝔥 →ₗ[R] R) (hα : α ∈ posRoots) (h : Δ.𝔥),
    ⁅(↑h : 𝔤), (↑(negRootVec α hα) : 𝔤)⁆ = -(α h) • (↑(negRootVec α hα) : 𝔤)
  ι_negRootVec_ne_zero : ∀ (α : Δ.𝔥 →ₗ[R] R) (hα : α ∈ posRoots),
    UniversalEnvelopingAlgebra.ι R (negRootVec α hα) ≠ 0
  uea_nminus_noZeroDivisors : NoZeroDivisors (UniversalEnvelopingAlgebra R ↥(Δ.𝔫_neg))
  uea_nminus_nontrivial : Nontrivial (UniversalEnvelopingAlgebra R ↥(Δ.𝔫_neg))
  posRootVec : ∀ α ∈ posRoots, ↥(Δ.𝔫_pos)
  posRootVec_weight : ∀ (α : Δ.𝔥 →ₗ[R] R) (hα : α ∈ posRoots) (h : Δ.𝔥),
    ⁅(↑h : 𝔤), (↑(posRootVec α hα) : 𝔤)⁆ = (α h) • (↑(posRootVec α hα) : 𝔤)
  npos_span : ∀ (e : Δ.𝔫_pos), ∃ (c : ∀ α ∈ posRoots, R),
    (e : 𝔤) = ∑ x ∈ posRoots.attach, c x.1 x.2 • (↑(posRootVec x.1 x.2) : 𝔤)

def PositiveRootData.IsInQPlus {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ) (μ : Δ.𝔥 →ₗ[R] R) : Prop :=
  ∃ (c : (Δ.𝔥 →ₗ[R] R) → ℕ), μ = ∑ α ∈ rd.posRoots, (c α) • α

noncomputable def IsVermaModule.maxProperSubmodule (hM : IsVermaModule Δ M wt) :
    LieSubmodule R 𝔤 M :=
  sSup {N : LieSubmodule R 𝔤 M | N ≠ ⊤}

noncomputable abbrev IsVermaModule.simpleQuotient (hM : IsVermaModule Δ M wt) :=
  M ⧸ hM.maxProperSubmodule
-- Instances on the quotient transport automatically via the abbrev.

end UEASubalgHelpers

def vermaIdeal (Δ : TriangularDecomposition R 𝔤) (wt : Δ.𝔥 →ₗ[R] R) :
    RingCon (UniversalEnvelopingAlgebra R 𝔤) :=
  ringConGen (fun a b =>
    (∃ h : Δ.𝔥, a = UniversalEnvelopingAlgebra.ι R (h : 𝔤) ∧
               b = algebraMap R (UniversalEnvelopingAlgebra R 𝔤) (wt h)) ∨
    (∃ e : Δ.𝔫_pos, a = UniversalEnvelopingAlgebra.ι R (e : 𝔤) ∧ b = 0))

def VermaModule (Δ : TriangularDecomposition R 𝔤) (wt : Δ.𝔥 →ₗ[R] R) :
    Type _ :=
  (vermaIdeal Δ wt).Quotient

instance VermaModule.instRing (Δ : TriangularDecomposition R 𝔤) (wt : Δ.𝔥 →ₗ[R] R) :
    Ring (VermaModule Δ wt) :=
  inferInstanceAs (Ring (vermaIdeal Δ wt).Quotient)

instance VermaModule.instAddCommGroup (Δ : TriangularDecomposition R 𝔤) (wt : Δ.𝔥 →ₗ[R] R) :
    AddCommGroup (VermaModule Δ wt) :=
  inferInstanceAs (AddCommGroup (vermaIdeal Δ wt).Quotient)

instance VermaModule.instModule (Δ : TriangularDecomposition R 𝔤) (wt : Δ.𝔥 →ₗ[R] R) :
    Module R (VermaModule Δ wt) :=
  ((vermaIdeal Δ wt).mk'.comp (algebraMap R (UniversalEnvelopingAlgebra R 𝔤))).toModule

def VermaModule.highestWeightVec (Δ : TriangularDecomposition R 𝔤) (wt : Δ.𝔥 →ₗ[R] R) :
    VermaModule Δ wt :=
  (vermaIdeal Δ wt).toQuotient 1

theorem liftQ_comp_quotKerEquiv_symm_apply
    {M₀ : Type*} [AddCommGroup M₀] [Module R M₀]
    {N₁ N₂ : Type*} [AddCommGroup N₁] [Module R N₁] [AddCommGroup N₂] [Module R N₂]
    (f₁ : M₀ →ₗ[R] N₁) (hf₁ : Function.Surjective f₁)
    (f₂ : M₀ →ₗ[R] N₂) (h : f₁.ker ≤ f₂.ker) (m : M₀) :
    (f₁.ker.liftQ f₂ h) ((f₁.quotKerEquivOfSurjective hf₁).symm (f₁ m)) = f₂ m := by
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply]; rfl

def lieModuleEquivOfSurjEqKer
    {M₀ V₁ V₂ : Type*}
    [AddCommGroup M₀] [Module R M₀] [LieRingModule 𝔤 M₀] [LieModule R 𝔤 M₀]
    [AddCommGroup V₁] [Module R V₁] [LieRingModule 𝔤 V₁] [LieModule R 𝔤 V₁]
    [AddCommGroup V₂] [Module R V₂] [LieRingModule 𝔤 V₂] [LieModule R 𝔤 V₂]
    (η₁ : M₀ →ₗ⁅R,𝔤⁆ V₁) (hη₁ : Function.Surjective η₁)
    (η₂ : M₀ →ₗ⁅R,𝔤⁆ V₂) (hη₂ : Function.Surjective η₂)
    (hker : η₁.ker = η₂.ker) : V₁ ≃ₗ⁅R,𝔤⁆ V₂ := by
  have hker_sub : η₁.toLinearMap.ker = η₂.toLinearMap.ker :=
    congr_arg LieSubmodule.toSubmodule hker
  have h12 : η₁.toLinearMap.ker ≤ η₂.toLinearMap.ker := le_of_eq hker_sub
  have h21 : η₂.toLinearMap.ker ≤ η₁.toLinearMap.ker := le_of_eq hker_sub.symm

  let f_lin : V₁ →ₗ[R] V₂ :=
    (η₁.toLinearMap.ker.liftQ η₂.toLinearMap h12).comp
      (η₁.toLinearMap.quotKerEquivOfSurjective hη₁).symm.toLinearMap

  let g_lin : V₂ →ₗ[R] V₁ :=
    (η₂.toLinearMap.ker.liftQ η₁.toLinearMap h21).comp
      (η₂.toLinearMap.quotKerEquivOfSurjective hη₂).symm.toLinearMap

  have hf : ∀ m, f_lin (η₁ m) = η₂ m := fun m =>
    liftQ_comp_quotKerEquiv_symm_apply η₁.toLinearMap hη₁ η₂.toLinearMap h12 m
  have hg : ∀ m, g_lin (η₂ m) = η₁ m := fun m =>
    liftQ_comp_quotKerEquiv_symm_apply η₂.toLinearMap hη₂ η₁.toLinearMap h21 m
  exact LieModuleEquiv.mk
    { toLinearMap := f_lin
      map_lie' := by
        intro x v₁; obtain ⟨m, rfl⟩ := hη₁ v₁
        change f_lin (⁅x, η₁ m⁆) = ⁅x, f_lin (η₁ m)⁆
        rw [← η₁.map_lie, hf, hf, η₂.map_lie] }
    g_lin
    (fun v₁ => by
      obtain ⟨m, rfl⟩ := hη₁ v₁; change g_lin (f_lin (η₁ m)) = η₁ m; rw [hf, hg])
    (fun v₂ => by
      obtain ⟨m, rfl⟩ := hη₂ v₂; change f_lin (g_lin (η₂ m)) = η₂ m; rw [hg, hf])

end TriangularDecomposition

end
