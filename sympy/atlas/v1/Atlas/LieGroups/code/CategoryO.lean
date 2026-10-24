/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CategoryO.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.LieGroups.code.VermaModules
import Lemma.Int.WeightSubspace.eq.ToSubmoduleWeightSpace
import Lemma.Int.Any_All_Eq.of.LeKer_Ker.Surjective
import Lemma.Int.IsIntegral
import sympy.atlas.v1.Atlas.LieGroups.code.HarishChandraIsomorphism
import sympy.atlas.v1.Atlas.LieGroups.code.HilbertNoether
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis

noncomputable section

variable (R : Type*) [CommRing R]
variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]
variable {R 𝔤}

def HasWeightDecomposition (Δ : TriangularDecomposition R 𝔤)
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M] : Prop :=
  ∀ m : M, ∃ (S : Finset (Δ.𝔥 →ₗ[R] R)) (v : (μ : Δ.𝔥 →ₗ[R] R) → WeightSpace Δ M μ),
    m = ∑ μ ∈ S, (v μ : M)

structure IsCategoryO (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ)
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M] where
  finitely_generated : ∃ (S : Finset M), LieSubmodule.lieSpan R 𝔤 (S : Set M) = ⊤
  weight_decomp : HasWeightDecomposition Δ M
  weight_bound : ∃ (bds : Finset (Δ.𝔥 →ₗ[R] R)),
    ∀ μ ∈ weights Δ M, ∃ wt ∈ bds, rd.IsInQPlus (wt - μ)

def WeightLE {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ) (μ wt : Δ.𝔥 →ₗ[R] R) : Prop :=
  rd.IsInQPlus (wt - μ)

def ReflectionLT {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ) (α : Δ.𝔥 →ₗ[R] R) (μ wt : Δ.𝔥 →ₗ[R] R) : Prop :=
  α ∈ rd.posRoots ∧ ∃ (n : ℕ), 0 < n ∧ rd.corootPairing wt α = (n : R) ∧ μ = wt - n • α

def BruhatLE {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ) (μ wt : Δ.𝔥 →ₗ[R] R) : Prop :=
  Relation.ReflTransGen (fun a b => ∃ α, ReflectionLT rd α a b) μ wt

section CategoryOResults

variable {Δ : TriangularDecomposition R 𝔤}
variable {rd : PositiveRootData Δ}
variable {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]

def GeneralizedEigenspaceCenter
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (ueaAct : UniversalEnvelopingAlgebra R 𝔤 →ₐ[R] Module.End R M)
    (chi : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) →ₐ[R] R) :
    Submodule R M where
  carrier := {m : M | ∀ (z : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤))),
    ∃ (n : ℕ), ((ueaAct (z : UniversalEnvelopingAlgebra R 𝔤) -
      chi z • (LinearMap.id : Module.End R M)) ^ n : Module.End R M) m = 0}
  add_mem' := by

    intro a b ha hb z
    obtain ⟨na, hna⟩ := ha z
    obtain ⟨nb, hnb⟩ := hb z
    set T : Module.End R M := ueaAct (z : UniversalEnvelopingAlgebra R 𝔤) -
      chi z • (LinearMap.id : Module.End R M) with hT_def
    use na + nb

    have hlin := (T ^ (na + nb)).map_add a b
    rw [hlin]

    have ha0 : (T ^ (na + nb)) a = 0 := by
      have h1 : T ^ (na + nb) = T ^ nb * T ^ na := by
        rw [show na + nb = nb + na from Nat.add_comm na nb]; exact pow_add T nb na
      change (T ^ (na + nb)) a = 0
      rw [h1]; show (T ^ nb) ((T ^ na) a) = 0; rw [hna]; exact map_zero _

    have hb0 : (T ^ (na + nb)) b = 0 := by
      have h1 : T ^ (na + nb) = T ^ na * T ^ nb := pow_add T na nb
      change (T ^ (na + nb)) b = 0
      rw [h1]; show (T ^ na) ((T ^ nb) b) = 0; rw [hnb]; exact map_zero _

    rw [ha0, hb0, add_zero]

  zero_mem' := by
    intro z; exact ⟨0, by simp [pow_zero]⟩

  smul_mem' := by
    intro r m hm z
    obtain ⟨n, hn⟩ := hm z
    exact ⟨n, by simp [map_smul, hn]⟩

def IsInCategoryOChi
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (ueaAct : UniversalEnvelopingAlgebra R 𝔤 →ₐ[R] Module.End R M)
    (chi : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) →ₐ[R] R) : Prop :=
  IsCategoryO Δ rd M ∧
  GeneralizedEigenspaceCenter M ueaAct chi = ⊤

def GeneralizedEigenspaceCenter.toLieSubmodule
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (ueaAct : UniversalEnvelopingAlgebra R 𝔤 →ₐ[R] Module.End R M)
    (hcompat : ∀ (x : 𝔤) (m : M),
      ueaAct (UniversalEnvelopingAlgebra.ι R x) m = ⁅x, m⁆)
    (chi : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) →ₐ[R] R) :
    LieSubmodule R 𝔤 M :=
  { GeneralizedEigenspaceCenter M ueaAct chi with
    lie_mem := by
      intro x m hm z


      obtain ⟨n, hn⟩ := hm z
      use n

      have hcomm_uea : (z : UniversalEnvelopingAlgebra R 𝔤) *
        UniversalEnvelopingAlgebra.ι R x =
        UniversalEnvelopingAlgebra.ι R x * (z : UniversalEnvelopingAlgebra R 𝔤) := by
        have hz := z.property
        rw [Subalgebra.mem_center_iff] at hz
        exact (hz _).symm

      have hcomm_end : ueaAct (z : UniversalEnvelopingAlgebra R 𝔤) *
        ueaAct (UniversalEnvelopingAlgebra.ι R x) =
        ueaAct (UniversalEnvelopingAlgebra.ι R x) *
        ueaAct (z : UniversalEnvelopingAlgebra R 𝔤) := by
        rw [← map_mul, ← map_mul, hcomm_uea]

      set T : Module.End R M := ueaAct (z : UniversalEnvelopingAlgebra R 𝔤) -
        chi z • (LinearMap.id : Module.End R M) with hT_def
      set X : Module.End R M := ueaAct (UniversalEnvelopingAlgebra.ι R x)

      have hTX : T * X = X * T := by
        simp only [hT_def, sub_mul, mul_sub, hcomm_end]
        congr 1
        ext m₀
        simp [LinearMap.smul_apply, LinearMap.id_apply]

      have hTnX : T ^ n * X = X * T ^ n := Commute.pow_left hTX n

      have hxm : ⁅x, m⁆ = X m := (hcompat x m).symm
      rw [hxm]
      show (T ^ n) (X m) = 0
      have : (T ^ n) (X m) = (T ^ n * X) m := rfl
      rw [this, hTnX]
      show X ((T ^ n) m) = 0
      rw [hn, map_zero] }

noncomputable def idealStepFilt
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    {ι : Type*} (T : ι → Module.End R M) (N : Submodule R M) : Submodule R M :=
  ⨆ z : ι, Submodule.map (T z) N

noncomputable def idealChainFilt
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    {ι : Type*} (T : ι → Module.End R M) : ℕ → Submodule R M
  | 0 => ⊤
  | n + 1 => idealStepFilt T (idealChainFilt T n)

def WeylStabilizerModQ
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (x : Δ.𝔥 →ₗ[R] R) : Set wg.W :=
  {w : wg.W | ∃ (c : (Δ.𝔥 →ₗ[R] R) → ℤ),
    wg.dualAction w x - x = ∑ α ∈ rd.posRoots, c α • α}

def WeylStabilizer
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (_rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (x : Δ.𝔥 →ₗ[R] R) : Set wg.W :=
  {w : wg.W | wg.dualAction w x = x}

structure RootSystemWithReflections
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ) where
  allRoots : Finset (Δ.𝔥 →ₗ[R] R)
  posRoots_sub : ∀ α ∈ rd.posRoots, α ∈ allRoots
  roots_pos_or_neg : ∀ α ∈ allRoots, α ∈ rd.posRoots ∨ -α ∈ rd.posRoots
  reflection : (Δ.𝔥 →ₗ[R] R) → wg.W
  coroot : (Δ.𝔥 →ₗ[R] R) → Δ.𝔥
  corootPairing_eq_eval : ∀ α ∈ allRoots, ∀ μ : Δ.𝔥 →ₗ[R] R,
    rd.corootPairing μ α = μ (coroot α)
  reflection_formula : ∀ α ∈ allRoots, ∀ μ : Δ.𝔥 →ₗ[R] R,
    wg.dualAction (reflection α) μ = μ - (μ (coroot α)) • α
  reflection_order_two : ∀ α ∈ allRoots, reflection α * reflection α = 1
  allRoots_neg_closed : ∀ α ∈ allRoots, -α ∈ allRoots
  reflection_neg : ∀ α ∈ allRoots, reflection (-α) = reflection α
  reflection_conjugation : ∀ α ∈ allRoots, ∀ β ∈ allRoots,
    reflection α * reflection β * reflection α =
    reflection (wg.dualAction (reflection α) β)
  allRoots_reflection_closed : ∀ α ∈ allRoots, ∀ β ∈ allRoots,
    wg.dualAction (reflection α) β ∈ allRoots
  dualAction_sub : ∀ (w : wg.W) (μ ν : Δ.𝔥 →ₗ[R] R),
    wg.dualAction w (μ - ν) = wg.dualAction w μ - wg.dualAction w ν
  dualAction_zsmul : ∀ (w : wg.W) (n : ℤ) (μ : Δ.𝔥 →ₗ[R] R),
    wg.dualAction w (n • μ) = n • wg.dualAction w μ
  dualAction_rootLattice : ∀ (w : wg.W) (c : (Δ.𝔥 →ₗ[R] R) → ℤ),
    ∃ (c' : (Δ.𝔥 →ₗ[R] R) → ℤ),
      wg.dualAction w (∑ α ∈ rd.posRoots, c α • α) = ∑ α ∈ rd.posRoots, c' α • α
  pairing_integral : ∀ (α : Δ.𝔥 →ₗ[R] R), α ∈ allRoots →
    ∀ (μ : Δ.𝔥 →ₗ[R] R),
    (∃ (c : (Δ.𝔥 →ₗ[R] R) → ℤ),
      -(μ (coroot α)) • α = ∑ γ ∈ rd.posRoots, c γ • γ) →
    ∃ (n : ℤ), μ (coroot α) = (n : R)
  generated_by_reflections : ∀ w : wg.W, ∃ (n : ℕ) (αs : Fin n → Δ.𝔥 →ₗ[R] R),
    (∀ i, αs i ∈ allRoots) ∧
    w = (List.ofFn (fun i => reflection (αs i))).prod
  ρ_eq_half_sum : (2 : R) • wg.ρ = rd.sumPosRoots

def rootsOfStabilizer
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (rs : RootSystemWithReflections rd wg)
    (x : Δ.𝔥 →ₗ[R] R) : Set (Δ.𝔥 →ₗ[R] R) :=
  {α | α ∈ rs.allRoots ∧ rs.reflection α ∈ WeylStabilizerModQ rd wg x}

def IsRootSubsystem
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (rs : RootSystemWithReflections rd wg)
    (S : Set (Δ.𝔥 →ₗ[R] R)) : Prop :=

  (∀ α ∈ S, α ∈ rs.allRoots) ∧

  ((0 : Δ.𝔥 →ₗ[R] R) ∉ S) ∧

  (∀ α ∈ S, -α ∈ S) ∧

  (∀ α ∈ S, ∀ β ∈ S, wg.dualAction (rs.reflection α) β ∈ S)

def corootsOf
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {wg : WeylGroupData Δ}
    (rs : RootSystemWithReflections rd wg)
    (S : Set (Δ.𝔥 →ₗ[R] R)) : Set Δ.𝔥 :=
  {h : Δ.𝔥 | ∃ α ∈ S, h = rs.coroot α}
