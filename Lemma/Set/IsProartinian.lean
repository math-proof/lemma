import Mathlib
import Class.Patching_SystemTypes
import Instance.Deformations_Deformations_Lemmas
import Class.Deformations_IsProartinian
import Abbrev.Deformations_IsProartinian

set_option autoImplicit false

namespace AdicTopologyAux

variable {ι : Type*} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≥ ·)]
variable (α : ι → Type*) (f : ∀ i j, i ≤ j → α i → α j)
variable [∀ i, TopologicalSpace (α i)]
variable (hf : ∀ i j h, Continuous (f i j h))

include hf in
private lemma dense_inverseLimit_of_forall_image_dense
    (s : Set { v : Π i, α i // ∀ i j (h : i ≤ j), f i j h (v i) = v j })
    (hs : ∀ i, Dense ((fun x ↦ (Subtype.val x) i) '' s)) : Dense s := by
  classical
  rw [dense_iff_inter_open]
  rintro U ⟨t, ht, rfl⟩ ⟨x, hx⟩
  obtain ⟨I, u, hu₁, hu₂⟩ := isOpen_pi_iff.mp ht _ hx
  obtain ⟨i, hi⟩ := Finset.exists_le (α := ιᵒᵈ) I
  let U : Set (α i) := ⋂ (j : I), (f _ _ (hi j.1 j.2)) ⁻¹' u _
  have hU : IsOpen U := isOpen_iInter_of_finite fun j ↦ (hu₁ j.1 j.2).1.preimage (hf ..)
  obtain ⟨_, hz₁, z, hz₂, rfl⟩ := dense_iff_inter_open.mp (hs i) U hU
    ⟨x.1 _, by simp [U, x.2, hu₁]⟩
  exact ⟨z, hu₂ (by simpa [U, z.2] using hz₁), hz₂⟩

include hf in
lemma denseRange_inverseLimit {β}
    (g : β → { v : Π i, α i // ∀ i j (h : i ≤ j), f i j h (v i) = v j })
    (hg : ∀ i, DenseRange (fun x ↦ (g x).1 i)) : DenseRange g := by
  refine dense_inverseLimit_of_forall_image_dense α f hf _ fun i ↦ ?_
  rw [← Set.range_comp]
  exact hg _

end AdicTopologyAux

section AdicTopology

variable (R : Type*) [CommRing R] [IsLocalRing R] [TopologicalSpace R] [IsTopologicalRing R]

namespace IsLocalRing

variable [IsAdicTopology R]

lemma isOpen_maximalIdeal_pow'' (n : ℕ) : IsOpen (X := R) ↑(maximalIdeal R ^ n) :=
  (isAdic_iff.mp IsLocalRing.IsAdicTopology.isAdic).1 _

lemma isOpen_maximalIdeal' : IsOpen (X := R) (maximalIdeal R) :=
  pow_one (maximalIdeal R) ▸ isOpen_maximalIdeal_pow'' R 1

open Filter Topology in
lemma hasBasis_maximalIdeal_pow :
    Filter.HasBasis (𝓝 (0 : R)) (fun _ ↦ True) fun n ↦ ↑(maximalIdeal R ^ n) :=
  IsLocalRing.IsAdicTopology.isAdic (R := R) ▸ Ideal.hasBasis_nhds_zero_adic (maximalIdeal R)

lemma compactSpace_of_finite_residueField [IsNoetherianRing R] [Finite (ResidueField R)]
    [IsAdicComplete (maximalIdeal R) R] :
    CompactSpace R := by
  let f : R →+* Π i : ℕ, R ⧸ (maximalIdeal R) ^ i := algebraMap _ _
  have : Finite (R ⧸ maximalIdeal R) := ‹_›
  have : ∀ i, Finite (R ⧸ (maximalIdeal R) ^ i) := fun i ↦
    Ideal.finite_quotient_pow (IsNoetherian.noetherian _) _
  have hf : Continuous f := by continuity
  have : Topology.IsClosedEmbedding f := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [IsTopologicalAddGroup.isInducing_iff_nhds_zero]
      refine (f.map_zero ▸ (hf.tendsto 0).le_comap).antisymm ?_
      apply (hasBasis_maximalIdeal_pow R).ge_iff.mpr ?_
      rintro i -
      exact ⟨Set.pi {i} fun i ↦ {0}, set_pi_mem_nhds (Set.finite_singleton i) (by simp),
        by simp [Set.subset_def, f, Ideal.Quotient.eq_zero_iff_mem]⟩
    · change Function.Injective (RingHom.pi _)
      rw [injective_iff_map_eq_zero]
      intro a ha
      change a ∈ (⊥ : Ideal R)
      rw [← Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal R).ne_top]
      simpa [RingHom.pi, funext_iff, Ideal.Quotient.eq_zero_iff_mem] using ha
    · rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
      intro x hx
      obtain ⟨g, rfl⟩ : ∃ y : ℕ → R, x = fun i ↦ Ideal.Quotient.mk _ (y i) := by
        simp_rw [funext_iff]
        exact Classical.skolem (p := (x · = Ideal.Quotient.mk _ ·)).mp
          fun i ↦ by simpa only [eq_comm] using Ideal.Quotient.mk_surjective (x i)
      have : IsPrecomplete (maximalIdeal R) R := inferInstance
      have := mt (IsPrecomplete.prec this (f := g))
      simp_rw [← Ideal.one_eq_top, smul_eq_mul, mul_one] at this
      simp only [Set.mem_compl_iff, Set.mem_range, eq_comm, funext_iff, Pi.algebraMap_apply,
        Ideal.Quotient.algebraMap_eq, not_exists, not_forall, SModEq, Ideal.Quotient.mk_eq_mk, f]
          at hx this
      obtain ⟨i, j, e, H⟩ := this hx
      refine ⟨_, ?_, isOpen_set_pi ((Set.finite_singleton i).insert j)
        (s := fun i ↦ {Ideal.Quotient.mk _ (g i)})
        (fun _ _ ↦ isOpen_discrete _), by simp⟩
      rintro _ hx ⟨x, rfl⟩
      simp only [Set.insert_pi, Set.singleton_pi, Set.mem_inter_iff, Set.mem_preimage,
        Function.eval, Pi.algebraMap_apply, Ideal.Quotient.algebraMap_eq, Set.mem_singleton_iff,
        f] at hx
      obtain ⟨hx₁, hx₂⟩ := hx
      apply_fun Ideal.quotientMap (maximalIdeal R ^ i) (.id R) (Ideal.pow_le_pow_right e) at hx₁
      simp [hx₂, H] at hx₁
  exact this.compactSpace

lemma Continuous.of_isLocalHom {R S : Type*} [CommRing R] [IsLocalRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsAdicTopology R] [CommRing S] [IsLocalRing S] [TopologicalSpace S]
    [IsTopologicalRing S] [IsAdicTopology S] (f : R →+* S) [IsLocalHom f] : Continuous f := by
  apply continuous_of_continuousAt_zero
  unfold ContinuousAt
  rw [map_zero]
  apply ((hasBasis_maximalIdeal_pow R).tendsto_iff (hasBasis_maximalIdeal_pow S)).mpr ?_
  simp only [SetLike.mem_coe, true_and, forall_const, ← SetLike.le_def, ← Ideal.mem_comap,
    ← Ideal.map_le_iff_le_comap, Ideal.map_pow]
  intro n
  exact ⟨n, Ideal.pow_right_mono (((local_hom_TFAE f).out 0 2).mp ‹_›) _⟩

end IsLocalRing

end AdicTopology

section Proartinian

variable {R S : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]

lemma isProartinian_iff_isArtinianRing [DiscreteTopology R] :
    IsProartinian R ↔ IsArtinianRing R := by
  constructor <;> intro
  · have := IsProartinian.isArtinianRing_quotient (⊥ : Ideal R) (isOpen_discrete _)
    exact (RingEquiv.quotientBot R).surjective.isArtinianRing
  · exact ⟨fun I _ ↦ inferInstance⟩

section IsLocalRing

open IsLocalRing

variable [IsLocalRing R] [IsLocalRing S]

lemma isOpen_maximalIdeal_of_isProartinian [IsProartinian R] :
    IsOpen (X := R) (maximalIdeal R) := by
  obtain ⟨I, hI, hI'⟩ := IsLinearTopology.exists_ideal_isMaximal_and_isOpen R
  exact (isMaximal_iff _).mp hI ▸ hI'

lemma exists_maximalIdeal_pow_le_of_isProartinian [IsProartinian R]
    (I : Ideal R) (hI : IsOpen (X := R) I) :
    ∃ n, maximalIdeal R ^ n ≤ I := by
  by_cases hI' : I = ⊤
  · exact ⟨1, by simp [hI']⟩
  have := IsProartinian.isArtinianRing_quotient I hI
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hI'
  have : IsLocalRing (R ⧸ I) := .of_surjective' _ Ideal.Quotient.mk_surjective
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := R ⧸ I)
  rw [jacobson_eq_maximalIdeal _ bot_ne_top,
    ← IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective,
    ← Ideal.map_pow, Ideal.zero_eq_bot, ← le_bot_iff, Ideal.map_le_iff_le_comap,
    ← RingHom.ker, Ideal.mk_ker] at hn
  exact ⟨n, hn⟩

lemma isContinuous_of_isProartinian_of_isLocalHom
    [IsLocalRing.IsAdicTopology R]
    (f : R →+* S) [IsProartinian S] [IsLocalHom f] : Continuous f := by
  apply continuous_of_continuousAt_zero
  simp only [ContinuousAt, map_zero]
  rw [(IsLocalRing.hasBasis_maximalIdeal_pow R).tendsto_iff
    (IsLinearTopology.hasBasis_open_ideal (R := S))]
  intro I hI
  obtain ⟨n, hn⟩ := exists_maximalIdeal_pow_le_of_isProartinian I hI
  replace hn := (Ideal.pow_right_mono (((local_hom_TFAE f).out 0 2).mp ‹_›) n).trans hn
  rw [← Ideal.map_pow, Ideal.map_le_iff_le_comap] at hn
  exact ⟨n, trivial, hn⟩

lemma isLocalHom_of_isContinuous_of_isProartinian
    [IsProartinian R] (f : R →+* S) [IsProartinian S] (h : Continuous f) : IsLocalHom f := by
  constructor
  intro a ha
  by_contra ha'
  obtain ⟨n, hn⟩ := exists_maximalIdeal_pow_le_of_isProartinian ((maximalIdeal S).comap f)
    (isOpen_maximalIdeal_of_isProartinian.preimage h)
  refine hn (Ideal.pow_mem_pow ha' n) (by simpa using ha.pow n)

end IsLocalRing

end Proartinian
