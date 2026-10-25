/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ProductMeasure.Part2
import Theorem.StatisticalMechanics.Code.FK.Ergodicity
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneMergeGeom
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneMerge.Part4
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneUniqueness.Part3
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
open MeasureTheory Measure Set MeasurableSpace ProbabilityTheory Filter Finset
open scoped ENNReal NNReal Topology BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]


theorem bkc_infinitePi_disjoint_cylinder
    (μ : (i : ι) → Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    {s t : Finset ι} {S : Set (Π i : s, X i)} {T : Set (Π i : t, X i)}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hd : Disjoint s t) :
    Measure.infinitePi μ (cylinder s S ∩ cylinder t T)
      = Measure.infinitePi μ (cylinder s S) * Measure.infinitePi μ (cylinder t T) := by
  have hind : iIndepFun (fun i (ω : Π i, X i) => ω i) (Measure.infinitePi μ) :=
    iIndepFun_infinitePi (𝓧 := X) (X := fun _ x => x) (fun i => measurable_id)
  simpa only [cylinder] using
    (hind.indepFun_finset s t hd (fun e => measurable_pi_apply e)).measure_inter_preimage_eq_mul
      S T hS hT

omit [∀ i, MeasurableSpace (X i)] in


theorem bkc_projP_preimage_cylinder (p : ι → Prop) (s : Finset (Subtype p))
    (S : Set (Π j : s, X ((j : Subtype p) : ι))) :
    (fun (ω : Π i, X i) (j' : Subtype p) => ω (j' : ι)) ⁻¹' (cylinder s S)
      = cylinder (s.map (Function.Embedding.subtype p))
          ((fun (y : Π i : s.map (Function.Embedding.subtype p), X (i : ι)) (j : s) =>
              y ⟨((j : Subtype p) : ι),
                by rw [Finset.mem_map]; exact ⟨(j : Subtype p), j.2, rfl⟩⟩) ⁻¹' S) := by
  ext ω; simp only [Set.mem_preimage, mem_cylinder]; rfl


theorem bkc_infinitePi_map_piEquivPiSubtypeProd
    (μ : (i : ι) → Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (p : ι → Prop) [DecidablePred p] :
    (Measure.infinitePi μ).map (MeasurableEquiv.piEquivPiSubtypeProd X p)
      = (Measure.infinitePi (fun j : Subtype p => μ (j : ι))).prod
          (Measure.infinitePi (fun j : {i // ¬ p i} => μ (j : ι))) := by
  classical
  symm
  refine Measure.prod_eq_generateFrom generateFrom_measurableCylinders
    generateFrom_measurableCylinders isPiSystem_measurableCylinders isPiSystem_measurableCylinders
    ⟨fun _ => univ, fun _ => univ_mem_measurableCylinders _, fun _ => by simp,
      by rw [iUnion_const]⟩
    ⟨fun _ => univ, fun _ => univ_mem_measurableCylinders _, fun _ => by simp,
      by rw [iUnion_const]⟩
    ?_
  intro A hA B hB
  rw [mem_measurableCylinders] at hA hB
  obtain ⟨s₁, S₁, hS₁, rfl⟩ := hA
  obtain ⟨s₂, S₂, hS₂, rfl⟩ := hB
  rw [Measure.map_apply (MeasurableEquiv.piEquivPiSubtypeProd X p).measurable
    ((MeasurableSet.cylinder _ hS₁).prod (MeasurableSet.cylinder _ hS₂))]
  have hpre : (MeasurableEquiv.piEquivPiSubtypeProd X p) ⁻¹' (cylinder s₁ S₁ ×ˢ cylinder s₂ S₂)
      = ((fun (ω : Π i, X i) (j : Subtype p) => ω (j : ι)) ⁻¹' (cylinder s₁ S₁)) ∩
        ((fun (ω : Π i, X i) (j : {i // ¬ p i}) => ω (j : ι)) ⁻¹' (cylinder s₂ S₂)) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_inter_iff]
    rfl
  rw [hpre, bkc_projP_preimage_cylinder p s₁ S₁,
    bkc_projP_preimage_cylinder (fun i => ¬ p i) s₂ S₂]
  rw [bkc_infinitePi_disjoint_cylinder μ (?_) (?_) (?_)]
  · congr 1
    · rw [← bkc_projP_preimage_cylinder p s₁ S₁,
        ← Measure.map_apply (by fun_prop) (MeasurableSet.cylinder _ hS₁),
        Measure.map_infinitePi_infinitePi_of_inj (f := (Subtype.val : Subtype p → ι))
          Subtype.val_injective]
    · rw [← bkc_projP_preimage_cylinder (fun i => ¬ p i) s₂ S₂,
        ← Measure.map_apply (by fun_prop) (MeasurableSet.cylinder _ hS₂),
        Measure.map_infinitePi_infinitePi_of_inj (f := (Subtype.val : {i // ¬ p i} → ι))
          Subtype.val_injective]
  · exact (by fun_prop : Measurable _) hS₁
  · exact (by fun_prop : Measurable _) hS₂
  · rw [Finset.disjoint_left]
    intro a ha1 ha2
    rw [Finset.mem_map] at ha1 ha2
    obtain ⟨j1, _, rfl⟩ := ha1
    obtain ⟨j2, _, hj2⟩ := ha2
    simp only [Function.Embedding.subtype, Function.Embedding.coeFn_mk] at hj2
    exact j2.2 (hj2 ▸ j1.2)


theorem bkc_pi_absolutelyContinuous_fin :
    ∀ (n : ℕ) {Y : Fin n → Type*} [∀ k, MeasurableSpace (Y k)]
      (ν μ : (k : Fin n) → Measure (Y k))
      [∀ k, IsProbabilityMeasure (μ k)] [∀ k, IsProbabilityMeasure (ν k)],
      (∀ k, ν k ≪ μ k) → Measure.pi ν ≪ Measure.pi μ := by
  intro n
  induction n with
  | zero =>
    intro Y _ ν μ _ _ _
    have heq : Measure.pi ν = Measure.pi μ := by
      ext s _
      rcases Set.eq_empty_or_nonempty s with rfl | ⟨x, hx⟩
      · simp
      · have hsu : s = Set.univ := by
          ext y; simp only [Set.mem_univ, iff_true]; rwa [Subsingleton.elim y x]
        rw [hsu, measure_univ, measure_univ]
    rw [heq]
  | succ n ih =>
    intro Y _ ν μ _ _ h
    set e := MeasurableEquiv.piFinSuccAbove Y 0 with he
    have hμ : Measure.pi μ
        = ((μ 0).prod (Measure.pi fun j => μ (Fin.succAbove 0 j))).map e.symm := by
      rw [← (measurePreserving_piFinSuccAbove μ 0).map_eq, ← he,
        Measure.map_map e.symm.measurable e.measurable, MeasurableEquiv.symm_comp_self,
        Measure.map_id]
    have hν : Measure.pi ν
        = ((ν 0).prod (Measure.pi fun j => ν (Fin.succAbove 0 j))).map e.symm := by
      rw [← (measurePreserving_piFinSuccAbove ν 0).map_eq, ← he,
        Measure.map_map e.symm.measurable e.measurable, MeasurableEquiv.symm_comp_self,
        Measure.map_id]
    rw [hμ, hν]
    exact (Measure.AbsolutelyContinuous.prod (h 0)
      (ih (fun j => ν (Fin.succAbove 0 j)) (fun j => μ (Fin.succAbove 0 j))
        (fun j => h _))).map e.symm.measurable


theorem bkc_pi_absolutelyContinuous_fintype {κ : Type*} [Fintype κ] {Y : κ → Type*}
    [∀ k, MeasurableSpace (Y k)] (ν μ : (k : κ) → Measure (Y k))
    [∀ k, IsProbabilityMeasure (μ k)] [∀ k, IsProbabilityMeasure (ν k)]
    (h : ∀ k, ν k ≪ μ k) : Measure.pi ν ≪ Measure.pi μ := by
  classical
  set ee := Fintype.equivFin κ with hee
  have hmpμ := measurePreserving_piCongrLeft (fun k => μ k) ee.symm
  have hmpν := measurePreserving_piCongrLeft (fun k => ν k) ee.symm
  have hfin := bkc_pi_absolutelyContinuous_fin (Fintype.card κ)
    (fun n => ν (ee.symm n)) (fun n => μ (ee.symm n)) (fun n => h _)
  rw [← hmpμ.map_eq, ← hmpν.map_eq]
  exact hfin.map (MeasurableEquiv.piCongrLeft Y ee.symm).measurable


theorem bkc_infinitePi_ac_of_finite_diff
    (ν μ : (i : ι) → Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    [∀ i, IsProbabilityMeasure (ν i)]
    (F : Finset ι) (hdiff : ∀ i ∉ F, ν i = μ i) (hac : ∀ i, ν i ≪ μ i) :
    Measure.infinitePi ν ≪ Measure.infinitePi μ := by
  classical
  set p : ι → Prop := fun i => i ∈ F with hp
  set e := MeasurableEquiv.piEquivPiSubtypeProd X p with he
  have hsμ := bkc_infinitePi_map_piEquivPiSubtypeProd μ p
  have hsν := bkc_infinitePi_map_piEquivPiSubtypeProd ν p
  have heqrest : (fun j : {i // ¬ p i} => ν (j : ι)) = (fun j : {i // ¬ p i} => μ (j : ι)) := by
    funext j; exact hdiff (j : ι) j.2
  have hprodac : ((Measure.infinitePi (fun j : Subtype p => ν (j : ι))).prod
          (Measure.infinitePi (fun j : {i // ¬ p i} => ν (j : ι))))
      ≪ ((Measure.infinitePi (fun j : Subtype p => μ (j : ι))).prod
          (Measure.infinitePi (fun j : {i // ¬ p i} => μ (j : ι)))) := by
    rw [heqrest]
    refine Measure.AbsolutelyContinuous.prod ?_ (Measure.absolutelyContinuous_refl _)
    have : Fintype (Subtype p) := Fintype.ofFinite _
    rw [Measure.infinitePi_eq_pi, Measure.infinitePi_eq_pi]
    exact bkc_pi_absolutelyContinuous_fintype _ _ (fun j => hac _)
  calc Measure.infinitePi ν
      = ((Measure.infinitePi ν).map e).map e.symm := by
        rw [Measure.map_map e.symm.measurable e.measurable, MeasurableEquiv.symm_comp_self,
          Measure.map_id]
    _ ≪ ((Measure.infinitePi μ).map e).map e.symm := by
        rw [hsμ, hsν]; exact hprodac.map e.symm.measurable
    _ = Measure.infinitePi μ := by
        rw [Measure.map_map e.symm.measurable e.measurable, MeasurableEquiv.symm_comp_self,
          Measure.map_id]


end Percolation
end StatMech
