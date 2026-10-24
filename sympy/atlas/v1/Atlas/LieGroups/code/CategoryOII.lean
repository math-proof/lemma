/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CategoryOII.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.LieGroups.code.CategoryO
import Lemma.Int.IsInQPlus0
import Lemma.Int.Surjective_Comp.of.Surjective
import sympy.atlas.v1.Atlas.LieGroups.code.TensorHomAxiom

noncomputable section

open Classical

universe uCatO
universe u_V u_M u_P

variable (R : Type*) [CommRing R]
variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]
variable {R 𝔤}

def IsDominantWeightLE {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (lam : Δ.𝔥 →ₗ[R] R) : Prop :=
  ∀ (w : wg.W), w ∈ WeylStabilizerModQ rd wg lam →
    WeightLE rd lam (wg.dualAction w lam) → lam = wg.dualAction w lam

def IsDominantWeightBruhat {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (lam : Δ.𝔥 →ₗ[R] R) : Prop :=
  ∀ (w : wg.W), w ∈ WeylStabilizerModQ rd wg lam →
    BruhatLE rd lam (wg.dualAction w lam) → lam = wg.dualAction w lam

def NotNegIntCorootPairing
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (rs : RootSystemWithReflections rd wg)
    (lam : Δ.𝔥 →ₗ[R] R) : Prop :=
  ∀ α ∈ rd.posRoots, ¬ ∃ n : ℤ, n < 0 ∧ lam (rs.coroot α) = (n : R)

def IsIntegralDominantWeightBruhat
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (lam : Δ.𝔥 →ₗ[R] R) : Prop :=
  ∀ w : wg.W, w ∈ WeylStabilizerModQ rd wg lam → BruhatLE rd (wg.dualAction w lam) lam

def IsIntegralDominantWeightLE
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (lam : Δ.𝔥 →ₗ[R] R) : Prop :=
  ∀ w : wg.W, w ∈ WeylStabilizerModQ rd wg lam → WeightLE rd (wg.dualAction w lam) lam

def IsProjectiveInO {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (P : Type uCatO) [AddCommGroup P] [Module R P]
    [LieRingModule 𝔤 P] [LieModule R 𝔤 P]
    (_hP : IsCategoryO Δ rd P) : Prop :=
  ∀ (M : Type uCatO) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (_ : IsCategoryO Δ rd M),
  ∀ (N : Type uCatO) [AddCommGroup N] [Module R N]
    [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    (_ : IsCategoryO Δ rd N),
  ∀ (f : M →ₗ⁅R, 𝔤⁆ N) (_ : Function.Surjective f)
    (g : P →ₗ⁅R, 𝔤⁆ N),
    ∃ (h : P →ₗ⁅R, 𝔤⁆ M), ∀ p, f (h p) = g p

def IsInBlockO
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ)
    (_wg : WeylGroupData Δ)
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (lam : Δ.𝔥 →ₗ[R] R) : Prop :=
  IsCategoryO Δ rd M ∧


  ∃ (ueaAct : UniversalEnvelopingAlgebra R 𝔤 →ₐ[R] Module.End R M)
    (chi : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) →ₐ[R] R),
    GeneralizedEigenspaceCenter M ueaAct chi = ⊤

theorem verma_module_isCategoryO
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (wt : Δ.𝔥 →ₗ[R] R)
    (_hM : IsVermaModule Δ M wt) :
    IsCategoryO Δ rd M := by
  constructor
  ·
    refine ⟨{_hM.highestWeightVec}, ?_⟩
    simp only [Finset.coe_singleton]
    exact _hM.toIsHighestWeightModule.generates
  ·
    have hwd := _hM.toIsHighestWeightModule.weight_decomposition
    intro m
    have hm : m ∈ (⨆ (μ : Δ.𝔥 →ₗ[R] R), Δ.weightSubspace M μ : Submodule R M) := by
      rw [hwd]; exact Submodule.mem_top
    rw [Submodule.mem_iSup_iff_exists_finset] at hm
    obtain ⟨s, hms⟩ := hm
    rw [Submodule.mem_iSup_finset_iff_exists_sum] at hms
    obtain ⟨v, hv⟩ := hms
    exact ⟨s, fun μ => ⟨(v μ : M), (v μ).prop⟩, hv.symm⟩
  ·
    exact ⟨{wt}, fun μ hμ => ⟨wt, Finset.mem_singleton.mpr rfl,
      _hM.weight_subset_QPlus rd μ hμ⟩⟩


structure LieModule.CompositionSeriesOf
    {Δ : TriangularDecomposition R 𝔤}
    (_rd : PositiveRootData Δ)
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M] where
  length : ℕ
  series : Fin (length + 1) → LieSubmodule R 𝔤 M
  bot : series ⟨0, Nat.zero_lt_succ length⟩ = ⊥
  top : series ⟨length, Nat.lt_succ_iff.mpr le_rfl⟩ = ⊤
  strictly_increasing : ∀ i : Fin length, series i.castSucc < series i.succ
  quotients_irreducible : ∀ i : Fin length,
    LieModule.IsIrreducible R 𝔤
      (↥(series i.succ) ⧸ (series i.castSucc).comap (series i.succ).incl)

noncomputable instance prodLieRingModule : LieRingModule L' (M₁ × M₂) where
  bracket x m := (⁅x, m.1⁆, ⁅x, m.2⁆)
  add_lie x y m := by ext <;> exact add_lie ..
  lie_add x m n := by ext <;> exact lie_add ..
  leibniz_lie x y m := by ext <;> [exact leibniz_lie x y m.1; exact leibniz_lie x y m.2]

noncomputable instance prodLieModule : LieModule R' L' (M₁ × M₂) where
  smul_lie r x m := by ext <;> exact smul_lie ..
  lie_smul r x m := by ext <;> exact lie_smul ..

variable {N' : Type*} [AddCommGroup N'] [Module R' N']
    [LieRingModule L' N'] [LieModule R' L' N']

noncomputable def prodLieModuleHom
    (f₁ : M₁ →ₗ⁅R', L'⁆ N') (f₂ : M₂ →ₗ⁅R', L'⁆ N') :
    M₁ × M₂ →ₗ⁅R', L'⁆ N' where
  toFun m := f₁ m.1 + f₂ m.2
  map_add' m n := by simp [map_add, add_add_add_comm]
  map_smul' r m := by simp [map_smul, smul_add]
  map_lie' {x m} := by
    show f₁ ⁅x, m.1⁆ + f₂ ⁅x, m.2⁆ = ⁅x, f₁ m.1 + f₂ m.2⁆
    rw [lie_add, f₁.map_lie, f₂.map_lie]

omit [LieAlgebra R' L'] [LieModule R' L' M₁] [LieModule R' L' M₂] [LieModule R' L' N'] in
@[simp] lemma prodLieModuleHom_apply
    (f₁ : M₁ →ₗ⁅R', L'⁆ N') (f₂ : M₂ →ₗ⁅R', L'⁆ N') (m : M₁ × M₂) :
    prodLieModuleHom f₁ f₂ m = f₁ m.1 + f₂ m.2 := rfl

end ProdLieModule


def LieModule.CompositionSeriesOf.countFactorsIso
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (cs : LieModule.CompositionSeriesOf rd M)
    (L : Type*) [AddCommGroup L] [Module R L]
    [LieRingModule 𝔤 L] [LieModule R 𝔤 L] : ℕ :=
  Finset.card (Finset.univ.filter fun (i : Fin cs.length) =>
    Nonempty (L ≃ₗ⁅R, 𝔤⁆ (↥(cs.series i.succ) ⧸ (cs.series i.castSucc).comap (cs.series i.succ).incl)))

noncomputable def quotTopBotLieModuleEquiv
    {L : Type*} [AddCommGroup L] [Module R L]
    [LieRingModule 𝔤 L] [LieModule R 𝔤 L] :
    (↥(⊤ : LieSubmodule R 𝔤 L) ⧸
      ((⊥ : LieSubmodule R 𝔤 L).comap (⊤ : LieSubmodule R 𝔤 L).incl)) ≃ₗ⁅R,𝔤⁆ L := by
  have hbot_sub : ((⊥ : LieSubmodule R 𝔤 L).comap (⊤ : LieSubmodule R 𝔤 L).incl).toSubmodule = ⊥ := by
    have h : (⊥ : LieSubmodule R 𝔤 L).comap (⊤ : LieSubmodule R 𝔤 L).incl = ⊥ := by
      rw [LieSubmodule.comap_incl_eq_bot]; simp
    simp [h]
  exact {
    ((⊥ : LieSubmodule R 𝔤 L).comap (⊤ : LieSubmodule R 𝔤 L).incl).toSubmodule.quotEquivOfEqBot
      hbot_sub |>.trans (LinearEquiv.ofTop (⊤ : Submodule R L) rfl) with
    map_lie' := by
      intro x q
      induction q using Quotient.inductionOn'
      rfl
  }

noncomputable def LieModuleHom.liftQ
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {P : Type*} [AddCommGroup P] [Module R P]
    [LieRingModule 𝔤 P] [LieModule R 𝔤 P]
    {L : Type*} [AddCommGroup L] [Module R L]
    [LieRingModule 𝔤 L] [LieModule R 𝔤 L]
    {J : LieSubmodule R 𝔤 P}
    (f : P →ₗ⁅R, 𝔤⁆ L) (h : J ≤ f.ker) :
    (P ⧸ J) →ₗ⁅R, 𝔤⁆ L where
  toLinearMap := J.toSubmodule.liftQ f.toLinearMap (by
    intro x hx; exact LinearMap.mem_ker.mpr (LieModuleHom.mem_ker.mp (h hx)))
  map_lie' := by
    intro x m
    induction m using Quotient.inductionOn' with | h m =>
    show f ⁅x, m⁆ = ⁅x, f m⁆
    exact f.map_lie x m

noncomputable def homEquivThroughQuotient
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {P : Type*} [AddCommGroup P] [Module R P]
    [LieRingModule 𝔤 P] [LieModule R 𝔤 P]
    {L : Type*} [AddCommGroup L] [Module R L]
    [LieRingModule 𝔤 L] [LieModule R 𝔤 L]
    {J : LieSubmodule R 𝔤 P}
    (hfact : ∀ (f : P →ₗ⁅R, 𝔤⁆ L), J ≤ f.ker) :
    ((P ⧸ J) →ₗ⁅R, 𝔤⁆ L) ≃ₗ[R] (P →ₗ⁅R, 𝔤⁆ L) :=
  LinearEquiv.ofBijective
    { toFun := fun g => g.comp (LieSubmodule.Quotient.mk' J)
      map_add' := fun g₁ g₂ => by ext; simp
      map_smul' := fun r g => by ext; simp }
    ⟨by

      intro g₁ g₂ h
      ext ⟨m⟩
      exact LieModuleHom.congr_fun h m
    , by

      intro f
      exact ⟨LieModuleHom.liftQ f (hfact f), by
        ext p; rfl⟩
    ⟩
