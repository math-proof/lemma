/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RotationInvariance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TranslationInvariance.Part5
import Theorem.StatisticalMechanics.Code.FK.BulkDeviationProof.Part2
import Theorem.StatisticalMechanics.Code.FK.OffCentreSandwichProof.Part6
import Def.StatisticalMechanics.Code.FK.RotationInvariance.Part3
open MeasureTheory Filter Topology SimpleGraph Set
open StatMech.ConfigSpace StatMech.Lattice
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.style.openClassical false
set_option linter.style.longLine false
set_option linter.style.show false


namespace StatMech

namespace FK

open StatMech.Lattice

variable {d : ℕ}


theorem rot_map_centred_edge (S : BoxSym d) (w : Site d) :
    Sym2.map S.τ (s((0 : Site d), w) : Sym2 (Site d)) = s((0 : Site d), S.τ w) := by
  rw [Sym2.map_mk, rot_boxSym_fixes_zero S]


theorem rot_free_centred_unit_const (hd : 0 < d) (j : Fin d) (b : Bool) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) :
    freeEdgeDensity d 2 (s((0 : Site d), candMap d (0 : Site d) (j, b)) : Sym2 (Site d)) p
      = freeEdgeDensity d 2 (rot_refUnitEdge d hd) p := by
  
  have hpos : freeEdgeDensity d 2 (s((0 : Site d), candMap d (0 : Site d) (j, b)) : Sym2 (Site d)) p
      = freeEdgeDensity d 2 (s((0 : Site d), candMap d (0 : Site d) (j, true)) : Sym2 (Site d)) p := by
    cases b with
    | true => rfl
    | false =>
        rw [← rot_free_density_boxSym (fkTI_signFlip d j)
              (s((0 : Site d), candMap d (0 : Site d) (j, false)) : Sym2 (Site d)) hp hp1,
            rot_map_centred_edge, rot_signFlip_neg_to_pos]
  
  rw [hpos, ← rot_free_density_boxSym (rot_permBoxSym d (Equiv.swap (⟨0, hd⟩ : Fin d) j))
        (s((0 : Site d), candMap d (0 : Site d) (j, true)) : Sym2 (Site d)) hp hp1,
      rot_map_centred_edge]
  show freeEdgeDensity d 2 (s((0 : Site d),
        rot_permEquiv d (Equiv.swap (⟨0, hd⟩ : Fin d) j) (candMap d (0 : Site d) (j, true)))) p = _
  rw [rot_permEquiv_axis_to_zero j hd]
  rfl


theorem rot_wired_centred_unit_const (hd : 0 < d) (j : Fin d) (b : Bool) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) :
    wiredEdgeDensity d 2 (s((0 : Site d), candMap d (0 : Site d) (j, b)) : Sym2 (Site d)) p
      = wiredEdgeDensity d 2 (rot_refUnitEdge d hd) p := by
  have hpos : wiredEdgeDensity d 2 (s((0 : Site d), candMap d (0 : Site d) (j, b)) : Sym2 (Site d)) p
      = wiredEdgeDensity d 2 (s((0 : Site d), candMap d (0 : Site d) (j, true)) : Sym2 (Site d)) p := by
    cases b with
    | true => rfl
    | false =>
        rw [← rot_wired_density_boxSym (fkTI_signFlip d j)
              (s((0 : Site d), candMap d (0 : Site d) (j, false)) : Sym2 (Site d)) hp hp1,
            rot_map_centred_edge, rot_signFlip_neg_to_pos]
  rw [hpos, ← rot_wired_density_boxSym (rot_permBoxSym d (Equiv.swap (⟨0, hd⟩ : Fin d) j))
        (s((0 : Site d), candMap d (0 : Site d) (j, true)) : Sym2 (Site d)) hp hp1,
      rot_map_centred_edge]
  show wiredEdgeDensity d 2 (s((0 : Site d),
        rot_permEquiv d (Equiv.swap (⟨0, hd⟩ : Fin d) j) (candMap d (0 : Site d) (j, true)))) p = _
  rw [rot_permEquiv_axis_to_zero j hd]
  rfl


theorem rot_edge_dir (x y : Site d) (hadj : (hypercubicLattice d).Adj x y) :
    ∃ p : Fin d × Bool, y - x = candMap d (0 : Site d) p := by
  change NearestNeighbour d x y at hadj
  rw [nearestNeighbour_iff_shift] at hadj
  obtain ⟨j, s, hs, hys⟩ := hadj
  refine ⟨(j, decide (s = 1)), ?_⟩
  funext i
  show y i - x i = candMap d (0 : Site d) (j, decide (s = 1)) i
  rw [rot_candMap_apply, hys]
  show (Function.update x j (x j + s)) i - x i = _
  by_cases hi : i = j
  · subst hi; rw [Function.update_self]
    rcases hs with rfl | rfl <;> simp
  · rw [Function.update_of_ne hi]; simp [hi]


theorem rot_free_edge_const (hd : 0 < d) (x y : Site d)
    (hadj : (hypercubicLattice d).Adj x y) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    freeEdgeDensity d 2 (s(x, y) : Sym2 (Site d)) p = freeEdgeDensity d 2 (rot_refUnitEdge d hd) p := by
  obtain ⟨⟨j, b⟩, hdir⟩ := rot_edge_dir x y hadj
  rw [rot_free_density_recentre x y hp hp1, hdir]
  exact rot_free_centred_unit_const hd j b hp hp1


theorem rot_wired_edge_const (hd : 0 < d) (x y : Site d)
    (hadj : (hypercubicLattice d).Adj x y) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    wiredEdgeDensity d 2 (s(x, y) : Sym2 (Site d)) p = wiredEdgeDensity d 2 (rot_refUnitEdge d hd) p := by
  obtain ⟨⟨j, b⟩, hdir⟩ := rot_edge_dir x y hadj
  rw [rot_wired_density_recentre x y hp hp1, hdir]
  exact rot_wired_centred_unit_const hd j b hp hp1


theorem rot_free_box_edge_const (hd : 0 < d) (m : ℕ) (eb : Sym2 (boxVerts d m))
    (heb : eb ∈ (boxGraph d m).edgeFinset) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    freeEdgeDensity d 2 (edgeIncl d m eb) p = freeEdgeDensity d 2 (rot_refUnitEdge d hd) p := by
  rw [SimpleGraph.mem_edgeFinset] at heb
  induction eb with
  | h u v =>
    rw [SimpleGraph.mem_edgeSet, boxGraph, SimpleGraph.comap_adj] at heb
    show freeEdgeDensity d 2 (s((u : Site d), (v : Site d)) : Sym2 (Site d)) p = _
    exact rot_free_edge_const hd (u : Site d) (v : Site d) heb hp hp1


theorem rot_wired_box_edge_const (hd : 0 < d) (m : ℕ) (eb : Sym2 (boxVerts d m))
    (heb : eb ∈ (boxGraph d m).edgeFinset) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    wiredEdgeDensity d 2 (edgeIncl d m eb) p = wiredEdgeDensity d 2 (rot_refUnitEdge d hd) p := by
  rw [SimpleGraph.mem_edgeFinset] at heb
  induction eb with
  | h u v =>
    rw [SimpleGraph.mem_edgeSet, boxGraph, SimpleGraph.comap_adj] at heb
    show wiredEdgeDensity d 2 (s((u : Site d), (v : Site d)) : Sym2 (Site d)) p = _
    exact rot_wired_edge_const hd (u : Site d) (v : Site d) heb hp hp1


theorem rot_freeRotationResidue (hd : 0 < d) (N : ℕ) (e' : Sym2 (boxVerts d N))
    (he' : e' ∈ (boxGraph d N).edgeFinset) (t : ℝ) :
    ocs_FreeRotationResidue (d := d) N e' t := by
  intro m eb heb
  rw [rot_free_box_edge_const hd m eb heb (fsc_logistic_pos t) (fsc_logistic_lt_one t),
      rot_free_box_edge_const hd N e' he' (fsc_logistic_pos t) (fsc_logistic_lt_one t)]


theorem rot_wiredRotationResidue (hd : 0 < d) (N : ℕ) (e' : Sym2 (boxVerts d N))
    (he' : e' ∈ (boxGraph d N).edgeFinset) (t : ℝ) :
    ocs_WiredRotationResidue (d := d) N e' t := by
  intro m eb heb
  rw [rot_wired_box_edge_const hd m eb heb (fsc_logistic_pos t) (fsc_logistic_lt_one t),
      rot_wired_box_edge_const hd N e' he' (fsc_logistic_pos t) (fsc_logistic_lt_one t)]


theorem rot_freeRotationResidue_edges (hd : 0 < d) (N : ℕ) (e' : Sym2 (boxVerts d N))
    (he' : e' ∈ (boxGraph d N).edgeFinset) (t : ℝ) :
    ocs_FreeRotationResidue (d := d) N e' t :=
  rot_freeRotationResidue hd N e' he' t


theorem rot_wiredRotationResidue_edges (hd : 0 < d) (N : ℕ) (e' : Sym2 (boxVerts d N))
    (he' : e' ∈ (boxGraph d N).edgeFinset) (t : ℝ) :
    ocs_WiredRotationResidue (d := d) N e' t :=
  rot_wiredRotationResidue hd N e' he' t


set_option maxHeartbeats 1000000 in


theorem rot_fk_uniqueness_of_diag (hd : 1 ≤ d) (N : ℕ) (eb : Sym2 (boxVerts d N))
    (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
    {g : ℝ → ℝ} (hg : ConvexOn ℝ univ g)
    (hboxfree : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2 t) atTop (𝓝 (g t)))
    (hfreeDiag : ∀ (e' : Sym2 (boxVerts d N)), e' ∉ (boxGraph d N).edgeFinset →
      ∀ (t : ℝ), ocs_FreeRotationResidue (d := d) N e' t)
    (hwiredDiag : ∀ (e' : Sym2 (boxVerts d N)), e' ∉ (boxGraph d N).edgeFinset →
      ∀ (t : ℝ), ocs_WiredRotationResidue (d := d) N e' t) :
    {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧
        eventMassProb (fuc_freeMass d N t) A
          ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable :=
  ocs_fk_uniqueness_of_rotation hd N eb hEbox hg hboxfree
    (fun e' t => by
      by_cases he' : e' ∈ (boxGraph d N).edgeFinset
      · exact rot_freeRotationResidue hd N e' he' t
      · exact hfreeDiag e' he' t)
    (fun e' t => by
      by_cases he' : e' ∈ (boxGraph d N).edgeFinset
      · exact rot_wiredRotationResidue hd N e' he' t
      · exact hwiredDiag e' he' t)

end FK
end StatMech
