import Mathlib
import Lemma.LocalLanglands.HeckePair
import Structure.LocalLanglands_HeckeCosetSystem

set_option autoImplicit false

open scoped Pointwise ENNReal
open MulAction MeasureTheory

namespace HeckeIntegralSeam

section CosetSystem

variable {G : Type*} [Group G]

theorem mem_smul_coe_iff {y x : G} :
    x ∈ y • (U : Set G) ↔ (QuotientGroup.mk y : G ⧸ U) = QuotientGroup.mk x := by
  rw [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul, SetLike.mem_coe, QuotientGroup.eq]

theorem mulSet_subset_doubleCoset : (U : Set G) * {g} ⊆ HeckePair.doubleCoset U g := by
  intro x hx
  obtain ⟨u, hu, w, hw, rfl⟩ := Set.mem_mul.mp hx
  obtain rfl : w = g := hw
  exact HeckePair.mem_doubleCoset_iff.mpr ⟨u, hu, 1, one_mem U, by group⟩

theorem out_mk_mem_doubleCoset {x : G} (hx : x ∈ HeckePair.doubleCoset U g) :
    Quotient.out (QuotientGroup.mk x : G ⧸ U) ∈ HeckePair.doubleCoset U g := by
  have hmem : Quotient.out (QuotientGroup.mk x : G ⧸ U) ∈ x • (U : Set G) :=
    mem_smul_coe_iff.mpr (QuotientGroup.out_eq' _).symm
  obtain ⟨u, hu, hux⟩ := Set.mem_smul_set.mp hmem
  rw [← hux, smul_eq_mul]
  exact HeckePair.doubleCoset_mul_mem hx hu

namespace IsHeckeCosetSystem

variable {ι : Type*} {reps : ι → G}

theorem smul_subset (hsys : IsHeckeCosetSystem U g reps) (i : ι) :
    reps i • (U : Set G) ⊆ HeckePair.doubleCoset U g := by
  intro x hx
  obtain ⟨u, hu, rfl⟩ := Set.mem_smul_set.mp hx
  rw [smul_eq_mul]
  exact HeckePair.doubleCoset_mul_mem (hsys.mem_doubleCoset i) hu

theorem doubleCoset_eq_iUnion (hsys : IsHeckeCosetSystem U g reps) :
    HeckePair.doubleCoset U g = ⋃ i, reps i • (U : Set G) := by
  refine Set.Subset.antisymm (fun x hx => ?_) (Set.iUnion_subset fun i => hsys.smul_subset i)
  obtain ⟨i, hi⟩ := hsys.covers x hx
  exact Set.mem_iUnion.mpr ⟨i, mem_smul_coe_iff.mpr hi.symm⟩

theorem disjoint (hsys : IsHeckeCosetSystem U g reps) {i j : ι} (hij : i ≠ j) :
    Disjoint (reps i • (U : Set G)) (reps j • (U : Set G)) := by
  refine Set.disjoint_left.mpr fun x hxi hxj => hij ?_
  exact hsys.mk_injective ((mem_smul_coe_iff.mp hxi).trans (mem_smul_coe_iff.mp hxj).symm)

theorem reps_injective (hsys : IsHeckeCosetSystem U g reps) : Function.Injective reps :=
  fun i j hij => hsys.mk_injective (by simp only [hij])

end IsHeckeCosetSystem

theorem canonical_isHeckeCosetSystem
    (hfin : (QuotientGroup.mk '' ((U : Set G) * {g}) : Set (G ⧸ U)).Finite) :
    IsHeckeCosetSystem U g (fun q : ↥hfin.toFinset => Quotient.out (q : G ⧸ U)) := by
  constructor
  · rintro ⟨q, hq⟩
    rw [Set.Finite.mem_toFinset] at hq
    obtain ⟨z, hz, rfl⟩ := hq
    exact out_mk_mem_doubleCoset (mulSet_subset_doubleCoset hz)
  · intro x hx
    have hmk : (QuotientGroup.mk x : G ⧸ U) ∈ hfin.toFinset := by
      rw [Set.Finite.mem_toFinset, ← HeckePair.image_mk_doubleCoset g]
      exact Set.mem_image_of_mem _ hx
    exact ⟨⟨QuotientGroup.mk x, hmk⟩, (QuotientGroup.out_eq' _).symm⟩
  · intro q q' h
    refine Subtype.ext ?_
    have h' : QuotientGroup.mk (Quotient.out (q : G ⧸ U))
        = QuotientGroup.mk (Quotient.out (q' : G ⧸ U)) := h
    rwa [QuotientGroup.out_eq', QuotientGroup.out_eq'] at h'

end CosetSystem

section Volume

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
variable {U : Subgroup G} {g : G}

theorem smul_coe_eq_preimage (y : G) :
    y • (U : Set G) = (fun x => y⁻¹ * x) ⁻¹' (U : Set G) := by
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  rfl

theorem measurableSet_smul_coe (hU : MeasurableSet (U : Set G)) (y : G) :
    MeasurableSet (y • (U : Set G)) := by
  rw [smul_coe_eq_preimage]
  exact (measurable_const_mul y⁻¹) hU

theorem measure_smul_coe (μ : Measure G) [μ.IsMulLeftInvariant] (y : G) :
    μ (y • (U : Set G)) = μ (U : Set G) := by
  rw [smul_coe_eq_preimage]
  exact measure_preimage_mul μ y⁻¹ _

theorem IsHeckeCosetSystem.measure_doubleCoset {ι : Type*} [Fintype ι] {reps : ι → G}
    (hsys : IsHeckeCosetSystem U g reps) (μ : Measure G) [μ.IsMulLeftInvariant]
    (hU : MeasurableSet (U : Set G)) :
    μ (HeckePair.doubleCoset U g) = (Fintype.card ι : ENNReal) * μ (U : Set G) := by
  classical
  rw [hsys.doubleCoset_eq_iUnion]
  have hbU : (⋃ i, reps i • (U : Set G))
      = ⋃ i ∈ (Finset.univ : Finset ι), reps i • (U : Set G) := by
    simp
  rw [hbU, measure_biUnion_finset (fun i _ j _ hij => hsys.disjoint hij)
    (fun i _ => measurableSet_smul_coe hU (reps i))]
  rw [Finset.sum_congr rfl fun i _ => measure_smul_coe μ (reps i), Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]

theorem IsHeckeCosetSystem.measurableSet_doubleCoset {ι : Type*} [Fintype ι] {reps : ι → G}
    (hsys : IsHeckeCosetSystem U g reps) (hU : MeasurableSet (U : Set G)) :
    MeasurableSet (HeckePair.doubleCoset U g) := by
  rw [hsys.doubleCoset_eq_iUnion]
  exact MeasurableSet.iUnion fun i => measurableSet_smul_coe hU (reps i)

end Volume

end HeckeIntegralSeam
