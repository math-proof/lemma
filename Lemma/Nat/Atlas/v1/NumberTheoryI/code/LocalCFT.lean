import Mathlib
import sympy.Basic
import Def.v1.Atlas.NumberTheoryI.code.LocalCFT.Part3
open Filter Set LocalArtinReciprocity LocalArtinMap
open scoped RestrictedProduct
open scoped Pointwise


namespace LocalArtinReciprocity

/--
[ext_eq_of_le_of_normGroup_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalCFT.lean)
-/
@[path]
lemma ext_eq_of_le_of_normGroup_eq
  {D : LocalArtinReciprocity}
  {i j : D.I}
-- given
  (hij : i ≤ j)
  (hn : D.normGroup i = D.normGroup j) :
-- imply
  i = j := by
-- proof
  have hle : D.normGroup i ≤ D.normGroup j := le_of_eq hn
  have hji : j ≤ i := D.normGroup_reflects_le hle
  exact le_antisymm hij hji

end LocalArtinReciprocity

namespace LocalArtinReciprocity

/--
[normGroup_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalCFT.lean)
-/
@[path]
lemma normGroup_injective
  {D : LocalArtinReciprocity}
  {i j : D.I}
-- given
  (h : D.normGroup i = D.normGroup j) :
-- imply
  i = j := by
-- proof
  obtain ⟨k, hik, hjk, hk⟩ := D.exists_sup i j
  have hi_eq_k : D.normGroup i = D.normGroup k := by rw [hk, h, inf_idem]
  have hj_eq_k : D.normGroup j = D.normGroup k := by rw [hk, h, inf_idem]
  have hieqk : i = k := D.ext_eq_of_le_of_normGroup_eq hik hi_eq_k
  have hjeqk : j = k := D.ext_eq_of_le_of_normGroup_eq hjk hj_eq_k
  rw [hieqk, hjeqk]

end LocalArtinReciprocity

namespace LocalArtinReciprocity

/--
[normGroup_map_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalCFT.lean)
-/
@[path]
lemma normGroup_map_injective
  {D : LocalArtinReciprocity} :
-- imply
  Function.Injective D.normGroup :=
-- proof
  fun _ _ h => D.normGroup_injective h

end LocalArtinReciprocity

namespace LocalArtinReciprocity

/--
[normGroup_finiteIndex](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalCFT.lean)
-/
@[path]
lemma normGroup_finiteIndex
  {D : LocalArtinReciprocity}
  {i : D.I} :
-- imply
  (D.normGroup i).FiniteIndex := by
-- proof
  rw [Subgroup.finiteIndex_iff_finite_quotient]
  exact Empty.Finite.of_equiv _ (D.artinMap_quotient_equiv i).symm.toEquiv

end LocalArtinReciprocity

namespace LocalArtinReciprocity

/--
[closed_finiteIndex_isOpen](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalCFT.lean)
-/
@[path]
lemma closed_finiteIndex_isOpen
  {D : LocalArtinReciprocity}
  [Group G]
  [TopologicalSpace G]
  [SeparatelyContinuousMul G]
  {H : Subgroup G}
  [H.FiniteIndex]
-- given
  (hclosed : IsClosed (H : Set G)) :
-- imply
  IsOpen (H : Set G) :=
-- proof
  H.isOpen_of_isClosed_of_finiteIndex hclosed

end LocalArtinReciprocity

namespace LocalArtinReciprocity

/--
[normGroup_isOpen](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalCFT.lean)
-/
@[path]
lemma normGroup_isOpen
  {D : LocalArtinReciprocity}
  {i : D.I} :
-- imply
  IsOpen (D.normGroup i : Set D.Kx) := by
-- proof
  haveI := D.normGroup_finiteIndex i
  exact closed_finiteIndex_isOpen (D.normGroup i) (D.normGroup_isClosed i)

end LocalArtinReciprocity

namespace LocalArtinReciprocity

/--
[restrictMap_jointly_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalCFT.lean)
-/
@[path]
lemma restrictMap_jointly_injective
  {D : LocalArtinReciprocity}
  {j k m : D.I}
  {g₁ g₂ : D.GalLK m}
-- given
  (hj : j ≤ m)
  (hk : k ≤ m)
  (hnorm : D.normGroup m = D.normGroup j ⊓ D.normGroup k)
  (hgj : D.restrictMap hj g₁ = D.restrictMap hj g₂)
  (hgk : D.restrictMap hk g₁ = D.restrictMap hk g₂) :
-- imply
  g₁ = g₂ := by
-- proof
  obtain ⟨x₁, rfl⟩ := D.artinMap_surjective m g₁
  obtain ⟨x₂, rfl⟩ := D.artinMap_surjective m g₂
  have hdiff_j : D.artinMap j (x₁ * x₂⁻¹) = 1 := by
    rw [map_mul, map_inv, ← D.artinMap_compat hj, ← D.artinMap_compat hj]
    rw [hgj, mul_inv_cancel]
  have hdiff_k : D.artinMap k (x₁ * x₂⁻¹) = 1 := by
    rw [map_mul, map_inv, ← D.artinMap_compat hk, ← D.artinMap_compat hk]
    rw [hgk, mul_inv_cancel]
  have hm_mem : x₁ * x₂⁻¹ ∈ D.normGroup m := by
    rwa [hnorm]
      ⟨(D.artinMap_ker j) ▸ MonoidHom.mem_ker.mpr hdiff_j,
        (D.artinMap_ker k) ▸ MonoidHom.mem_ker.mpr hdiff_k⟩
  have : D.artinMap m (x₁ * x₂⁻¹) = 1 := by
    rw [← D.artinMap_ker m] at hm_mem; exact MonoidHom.mem_ker.mp hm_mem
  rwa [map_mul, map_inv, mul_inv_eq_one] at this

end LocalArtinReciprocity

namespace LocalArtinReciprocity

/--
[artinMap_unique](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalCFT.lean)
-/
@[path]
lemma artinMap_unique
  {D : LocalArtinReciprocity}
-- given
  (θ₁ θ₂ : ∀ i, D.Kx →* D.GalLK i)
  (_h_surj₁ : ∀ i, Function.Surjective (θ₁ i))
  (_h_surj₂ : ∀ i, Function.Surjective (θ₂ i))
  (h_ker₁ : ∀ i, (θ₁ i).ker = D.normGroup i)
  (h_ker₂ : ∀ i, (θ₂ i).ker = D.normGroup i)
  (h_frob₁ : ∀ (j : D.J) (π : D.Kx), D.IsUniformizer π → θ₁ (D.unramifiedEmb j) π = D.frobElt j)
  (h_frob₂ : ∀ (j : D.J) (π : D.Kx), D.IsUniformizer π → θ₂ (D.unramifiedEmb j) π = D.frobElt j)
  (h_compat₁ : ∀ {i j : D.I} (h : i ≤ j) (x : D.Kx), D.restrictMap h (θ₁ j x) = θ₁ i x)
  (h_compat₂ : ∀ {i j : D.I} (h : i ≤ j) (x : D.Kx), D.restrictMap h (θ₂ j x) = θ₂ i x)
  (uniformizers_generate : Subgroup.closure {π : D.Kx | D.IsUniformizer π} = ⊤)
  (_h_LET : ∀ (U : Subgroup D.Kx), U.FiniteIndex → IsOpen (U : Set D.Kx) → ∃ i, D.normGroup i = U)
  (kab_eq_kpi_kunr : ∀ (π : D.Kx), D.IsUniformizer π → ∀ (i : D.I), ∃ (j : D.J) (k : D.I), π ∈ D.normGroup k ∧ ∃ (m : D.I), D.unramifiedEmb j ≤ m ∧ k ≤ m ∧ i ≤ m ∧ D.normGroup m = D.normGroup (D.unramifiedEmb j) ⊓ D.normGroup k) :
-- imply
  ∀ i (x : D.Kx), θ₁ i x = θ₂ i x := by
-- proof
  suffices h_unif : ∀ (π : D.Kx), D.IsUniformizer π → ∀ (i : D.I),
    θ₁ i π = θ₂ i π by
    intro i x
    have hx : x ∈ Subgroup.closure {π : D.Kx | D.IsUniformizer π} := by
      rw [uniformizers_generate]; exact Subgroup.mem_top x
    have key : ∀ y ∈ Subgroup.closure {π : D.Kx | D.IsUniformizer π},
      θ₁ i y = θ₂ i y := by
      apply Subgroup.closure_induction
      · intro y hy; exact h_unif y hy i
      · simp [map_one]
      · intro a b _ _ ha hb; simp only [map_mul]; rw [ha, hb]
      · intro a _ ha; simp only [map_inv]; rw [ha]
    exact key x hx
  intro π hπ i
  obtain ⟨j, k, hπk, m, hjm, hkm, him, hnorm_m⟩ := kab_eq_kpi_kunr π hπ i
  have h_agree_m : θ₁ m π = θ₂ m π := by
    have hj_eq : D.restrictMap hjm (θ₁ m π) = D.restrictMap hjm (θ₂ m π) := by
      rw [h_compat₁ hjm, h_compat₂ hjm, h_frob₁ j π hπ, h_frob₂ j π hπ]
    have hk_eq : D.restrictMap hkm (θ₁ m π) = D.restrictMap hkm (θ₂ m π) := by
      rw [h_compat₁ hkm, h_compat₂ hkm]
      have h1 : π ∈ (θ₁ k).ker := h_ker₁ k ▸ hπk
      have h2 : π ∈ (θ₂ k).ker := h_ker₂ k ▸ hπk
      rw [MonoidHom.mem_ker.mp h1, MonoidHom.mem_ker.mp h2]
    exact D.restrictMap_jointly_injective hjm hkm hnorm_m _ _ hj_eq hk_eq
  calc θ₁ i π = D.restrictMap him (θ₁ m π) := (h_compat₁ him π).symm
    _ = D.restrictMap him (θ₂ m π) := by rw [h_agree_m]
    _ = θ₂ i π := h_compat₂ him π

end LocalArtinReciprocity

namespace LocalArtinMap

/--
[proj_fiber_mem_nhds](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalCFT.lean)
-/
@[path]
lemma proj_fiber_mem_nhds
  {M : LocalArtinMap}
  {i : M.I}
  {g : M.GalAb} :
-- imply
  {h : M.GalAb | M.proj i h = M.proj i g} ∈ nhds g := by
-- proof
  have : {h : M.GalAb | M.proj i h = M.proj i g} = (M.proj i) ⁻¹' {M.proj i g} := by
    ext; simp
  rw [this]
  exact (M.proj_continuous i).isOpen_preimage _ (isOpen_discrete _) |>.mem_nhds rfl

end LocalArtinMap

namespace LocalArtinMap

/--
[proj_fiber_isOpen](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalCFT.lean)
-/
@[path]
lemma proj_fiber_isOpen
  {M : LocalArtinMap}
  {i : M.I}
  {c : M.GalLK i} :
-- imply
  IsOpen {g : M.GalAb | M.proj i g = c} := by
-- proof
  rw [isOpen_iff_mem_nhds]
  intro g hg
  simp only [Set.mem_setOf_eq] at hg
  rw [← hg]
  exact M.proj_fiber_mem_nhds i g

end LocalArtinMap

namespace LocalArtinMap

/--
[proj_fiber_isClosed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalCFT.lean)
-/
@[path]
lemma proj_fiber_isClosed
  {M : LocalArtinMap}
  {i : M.I}
  {c : M.GalLK i} :
-- imply
  IsClosed {g : M.GalAb | M.proj i g = c} := by
-- proof
  rw [isOpen_compl_iff.symm]
  have : {g : M.GalAb | M.proj i g = c}ᶜ = ⋃ (d : M.GalLK i) (_ : d ≠ c),
    {g : M.GalAb | M.proj i g = d} := by
    ext g
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
    constructor
    · intro h; exact ⟨M.proj i g, h, rfl⟩
    · rintro ⟨d, hd, hg⟩; rw [hg]; exact hd
  rw [this]
  exact isOpen_iUnion fun d => isOpen_iUnion fun _ => M.proj_fiber_isOpen i d

end LocalArtinMap


-- created on 2026-10-23
