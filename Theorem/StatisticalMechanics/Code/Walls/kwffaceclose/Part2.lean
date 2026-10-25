/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwffaceclose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.fwrfaceregion.Part3
import Theorem.StatisticalMechanics.Code.Walls.jcwcutsetwalk
import Theorem.StatisticalMechanics.Code.Ising.KWClosedWalkParity.Part14
import Theorem.StatisticalMechanics.Code.Ising.DualWalkBoundsClose.Part3
import Def.StatisticalMechanics.Code.Walls.kwffaceclose.Part2
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech

namespace Walls

open StatMech.Lattice StatMech.Ising

attribute [local instance] Classical.propDecidable


theorem kwf_walkParity_eq_faceParity {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (hnd : Vc.edges.Nodup) {x y : Site 2} (p : (hypercubicLattice 2).Walk x y) :
    walkParity (hypercubicLattice 2) (Vc.edges.toFinset) p
      = kwf_faceParity (fwr_faceInside Vc) p := by
  induction p with
  | nil => rfl
  | @cons u v w h q ih =>
    rw [walkParity_cons, kwf_faceParity, ih]
    congr 1
    exact decide_eq_decide.mpr (kwf_walkEdges_iff_faceCut Vc hnd h)


theorem kwf_latLinking_iff_faceCut {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (hnd : Vc.edges.Nodup) :
    kwf_LinkingEven (Vc.edges.toFinset)
      ↔ ∀ (x : Site 2) (p : (hypercubicLattice 2).Walk x x),
          kwf_faceParity (fwr_faceInside Vc) p = false := by
  constructor
  · intro h x p; rw [← kwf_walkParity_eq_faceParity Vc hnd p]; exact h x p
  · intro h x p; rw [kwf_walkParity_eq_faceParity Vc hnd p]; exact h x p


theorem kwf_linkingEven_of_vertexCoboundary {δ : Finset (Sym2 (Site 2))} (c : Site 2 → Bool)
    (hδ : ∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v → (s(u, v) ∈ δ ↔ c u ≠ c v)) :
    kwf_LinkingEven δ := by
  intro x p
  rw [walkParity_eq_xor_of_isCoboundary c (fun h => hδ h) p]
  cases c x <;> rfl


theorem kwf_chord_not_cut_be :
    s((![1, 1] : Site 2), (![2, 1] : Site 2)) ∉ jed_cutSet jcw_shiftFace := by
  have hadj : (hypercubicLattice 2).Adj (![1, 1] : Site 2) (![1, 0] : Site 2) :=
    jcw_adj 1 1 1 0 (by norm_num)
  have hshared : sharedPrimalEdge (![1, 1] : Site 2) (![1, 0] : Site 2)
      = s((![1, 1] : Site 2), (![2, 1] : Site 2)) := by
    rw [show (![1, 0] : Site 2) = ![(1:ℤ), 1 - 1] by norm_num, jed_sh_right 1 1]
    norm_num
  rw [← hshared, jed_mem_cutSet_iff _ hadj]
  simp only [jcw_shiftFace, site2_eq]; norm_num


theorem kwf_chord_not_cut_cf :
    s((![1, 2] : Site 2), (![2, 2] : Site 2)) ∉ jed_cutSet jcw_shiftFace := by
  have hadj : (hypercubicLattice 2).Adj (![1, 2] : Site 2) (![1, 1] : Site 2) :=
    jcw_adj 1 2 1 1 (by norm_num)
  have hshared : sharedPrimalEdge (![1, 2] : Site 2) (![1, 1] : Site 2)
      = s((![1, 2] : Site 2), (![2, 2] : Site 2)) := by
    rw [show (![1, 1] : Site 2) = ![(1:ℤ), 2 - 1] by norm_num, jed_sh_right 1 2]
    norm_num
  rw [← hshared, jed_mem_cutSet_iff _ hadj]
  simp only [jcw_shiftFace, site2_eq]; norm_num


theorem kwf_chord_not_cut_ef :
    s((![2, 1] : Site 2), (![2, 2] : Site 2)) ∉ jed_cutSet jcw_shiftFace := by
  have hadj : (hypercubicLattice 2).Adj (![2, 1] : Site 2) (![1, 1] : Site 2) :=
    jcw_adj 2 1 1 1 (by norm_num)
  have hshared : sharedPrimalEdge (![2, 1] : Site 2) (![1, 1] : Site 2)
      = s((![2, 1] : Site 2), (![2, 2] : Site 2)) := by
    rw [show (![1, 1] : Site 2) = ![(2:ℤ) - 1, 1] by norm_num, jed_sh_up 2 1]
    norm_num
  rw [← hshared, jed_mem_cutSet_iff _ hadj]
  simp only [jcw_shiftFace, site2_eq]; norm_num


theorem kwf_faceCut_not_vertexCoboundary :
    ¬ ∃ c : Site 2 → Bool, ∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v →
      (s(u, v) ∈ jed_cutSet jcw_shiftFace ↔ c u ≠ c v) := by
  rintro ⟨c, hc⟩
  have hbc : (hypercubicLattice 2).Adj (![1, 1] : Site 2) (![1, 2] : Site 2) :=
    jcw_adj 1 1 1 2 (by norm_num)
  have hbe : (hypercubicLattice 2).Adj (![1, 1] : Site 2) (![2, 1] : Site 2) :=
    jcw_adj 1 1 2 1 (by norm_num)
  have hcf : (hypercubicLattice 2).Adj (![1, 2] : Site 2) (![2, 2] : Site 2) :=
    jcw_adj 1 2 2 2 (by norm_num)
  have hef : (hypercubicLattice 2).Adj (![2, 1] : Site 2) (![2, 2] : Site 2) :=
    jcw_adj 2 1 2 2 (by norm_num)
  have hsplit : c (![1, 1] : Site 2) ≠ c (![1, 2] : Site 2) := (hc hbc).mp jcw_right_mem_cutSet
  have heq_be : ¬ (c (![1, 1] : Site 2) ≠ c (![2, 1] : Site 2)) :=
    fun h => kwf_chord_not_cut_be ((hc hbe).mpr h)
  have heq_cf : ¬ (c (![1, 2] : Site 2) ≠ c (![2, 2] : Site 2)) :=
    fun h => kwf_chord_not_cut_cf ((hc hcf).mpr h)
  have heq_ef : ¬ (c (![2, 1] : Site 2) ≠ c (![2, 2] : Site 2)) :=
    fun h => kwf_chord_not_cut_ef ((hc hef).mpr h)
  revert hsplit heq_be heq_cf heq_ef
  cases c (![1, 1] : Site 2) <;> cases c (![1, 2] : Site 2) <;>
    cases c (![2, 1] : Site 2) <;> cases c (![2, 2] : Site 2) <;> simp_all


theorem kwf_status :
    (∀ {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a), Vc.edges.Nodup →
      (kwf_LinkingEven (Vc.edges.toFinset)
        ↔ ∀ (x : Site 2) (p : (hypercubicLattice 2).Walk x x),
            kwf_faceParity (fwr_faceInside Vc) p = false))
    ∧ (¬ ∃ c : Site 2 → Bool, ∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v →
        (s(u, v) ∈ jed_cutSet jcw_shiftFace ↔ c u ≠ c v)) :=
  ⟨fun Vc hnd => kwf_latLinking_iff_faceCut Vc hnd, kwf_faceCut_not_vertexCoboundary⟩


end Walls
end StatMech
