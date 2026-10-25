/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CylinderDecayClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.IntegralDecayClose.Part5
import Theorem.StatisticalMechanics.Code.FK.FiniteVolumeShift.Part5
import Def.StatisticalMechanics.Code.FK.CylinderDecayClose.Part3
open MeasureTheory Filter Topology BoundedContinuousFunction SimpleGraph Set
open StatMech.ConfigSpace StatMech.Lattice
open scoped BigOperators


namespace StatMech

namespace FK

open StatMech.IsingFK

variable {d : ℕ}


variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]


theorem cdc_boxMultiOpenEvent_isIncreasing (N : ℕ) (t : Finset (Sym2 (boxVerts d N))) :
    IsIncreasing (cdc_boxMultiOpenEvent N t) := by
  intro a b hab ha eb heb
  have hle := hab eb
  rw [ha eb heb] at hle
  exact le_antisymm (by simp) hle


theorem cdc_multiOpenEvent_image_eq_boxRestrict (N : ℕ) (t : Finset (Sym2 (boxVerts d N))) :
    cdc_multiOpenEvent (t.image (edgeIncl d N))
      = boxRestrict d N ⁻¹' (cdc_boxMultiOpenEvent N t) := by
  ext ω
  simp only [cdc_multiOpenEvent, cdc_boxMultiOpenEvent, Set.mem_setOf_eq, Set.mem_preimage,
    boxRestrict, Finset.forall_mem_image]


theorem cdc_wired_multiOpenEvent_tendsto (N : ℕ) (t : Finset (Sym2 (boxVerts d N)))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    Tendsto (fun m => (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent (t.image (edgeIncl d N)))) atTop
      (𝓝 ((wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent (t.image (edgeIncl d N))))) := by
  rw [cdc_multiOpenEvent_image_eq_boxRestrict N t]
  exact fk_wired_infinite_measure N hp hp1 (cdc_boxMultiOpenEvent_isIncreasing N t)


theorem cdc_free_multiOpenEvent_tendsto (N : ℕ) (t : Finset (Sym2 (boxVerts d N)))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    Tendsto (fun m => (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent (t.image (edgeIncl d N)))) atTop
      (𝓝 ((freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent (t.image (edgeIncl d N))))) := by
  rw [cdc_multiOpenEvent_image_eq_boxRestrict N t]
  exact fk_free_infinite_measure N hp hp1 (cdc_boxMultiOpenEvent_isIncreasing N t)


theorem cdc_edge_mem_range (x y : Site d)
    {N : ℕ} (hx : x ∈ box d N) (hy : y ∈ box d N) :
    s(x, y) ∈ Set.range (edgeIncl d N) :=
  ⟨s(⟨x, hx⟩, ⟨y, hy⟩), by unfold edgeIncl; rw [Sym2.map_mk]⟩


theorem cdc_finset_in_box (s : Finset (Sym2 (Site d))) :
    ∃ (N : ℕ) (t : Finset (Sym2 (boxVerts d N))), s = t.image (edgeIncl d N) := by
  classical
  
  set rad : Sym2 (Site d) → ℕ := fun e => Sym2.lift
      ⟨fun x y => Finset.univ.sup (fun i => (x i).natAbs ⊔ (y i).natAbs),
        fun x y => by simp only [sup_comm]⟩ e with hrad
  have hrad_mk : ∀ x y : Site d,
      rad s(x, y) = Finset.univ.sup (fun i => (x i).natAbs ⊔ (y i).natAbs) := fun x y => rfl
  
  refine ⟨s.sup rad, ?_⟩
  set N := s.sup rad with hN
  
  have hmem : ∀ e ∈ s, e ∈ Set.range (edgeIncl d N) := by
    intro e he
    induction e using Sym2.ind with | _ x y =>
    have hle : Finset.univ.sup (fun i => (x i).natAbs ⊔ (y i).natAbs) ≤ N := by
      rw [hN, ← hrad_mk x y]
      exact Finset.le_sup he
    have hxi : ∀ i, (x i).natAbs ≤ N := fun i =>
      le_trans (le_trans (le_max_left _ ((y i).natAbs))
        (Finset.le_sup (f := fun i => (x i).natAbs ⊔ (y i).natAbs) (Finset.mem_univ i))) hle
    have hyi : ∀ i, (y i).natAbs ≤ N := fun i =>
      le_trans (le_trans (le_max_right ((x i).natAbs) _)
        (Finset.le_sup (f := fun i => (x i).natAbs ⊔ (y i).natAbs) (Finset.mem_univ i))) hle
    exact cdc_edge_mem_range x y hxi hyi
  
  refine ⟨s.attach.image (fun e => (hmem e.1 e.2).choose), ?_⟩
  rw [Finset.image_image]
  ext e
  simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists, Function.comp_apply]
  constructor
  · intro he
    exact ⟨e, he, (hmem e he).choose_spec⟩
  · rintro ⟨a, ha, rfl⟩
    rw [(hmem a ha).choose_spec]
    exact ha


end FK
end StatMech
