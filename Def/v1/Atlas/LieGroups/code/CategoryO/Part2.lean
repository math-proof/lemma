/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CategoryO.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.LieGroups.code.VermaModules.Part7
import Lemma.Int.WeightSubspace.eq.ToSubmoduleWeightSpace
import Lemma.Int.Any_All_Eq.of.LeKer_Ker.Surjective
import Lemma.Int.IsIntegral
import Structure.v1.Atlas.LieGroups.code.HarishChandraIsomorphism.Part2
import Instance.v1.Atlas.LieGroups.code.HilbertNoether
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import Structure.v1.Atlas.LieGroups.code.CategoryO


noncomputable section

variable (R : Type*) [CommRing R]

variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]

variable {R 𝔤}

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

end CategoryOResults
end
