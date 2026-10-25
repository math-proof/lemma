/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/OuterContourWindingClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.PeierlsOuterClose.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsContourFinal.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsSingleCircuit.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsBoundaryConnected.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
import Theorem.StatisticalMechanics.Code.Lattice.RotationSystemFaces.Part4
import Theorem.StatisticalMechanics.Code.Lattice.ContourEncodingClose.Part3
import Theorem.StatisticalMechanics.Code.Lattice.LeftFace.Part4
import Theorem.StatisticalMechanics.Code.Lattice.EnclosingLength.Part2
import Def.StatisticalMechanics.Code.Ising.OuterContourWindingClose.Part3
open MeasureTheory Filter Topology Finset SimpleGraph
open scoped BigOperators ENNReal


namespace StatMech

namespace Ising

open StatMech.Lattice

open StatMech.Percolation (anchorFinset)

attribute [local instance] Classical.propDecidable


theorem isoOriginCompletion_origin_false (n : ℕ) :
    glue (plusField 2) (isoOriginCompletion n) (origin 2) = false := by
  rw [glue_mem (plusField 2) (isoOriginCompletion n) (origin_mem_box n)]
  simp [isoOriginCompletion]


theorem isoOriginCompletion_ne_origin_true (n : ℕ) {x : Site 2} (hx : x ≠ origin 2) :
    glue (plusField 2) (isoOriginCompletion n) x = true := by
  by_cases hb : x ∈ box 2 n
  · rw [glue_mem (plusField 2) (isoOriginCompletion n) hb]
    simp [isoOriginCompletion, hx]
  · rw [glue_not_mem (plusField 2) (isoOriginCompletion n) hb]; rfl


theorem isoOriginCompletion_minusCluster (n : ℕ) :
    minusCluster (glue (plusField 2) (isoOriginCompletion n)) (origin 2)
      = (↑({origin 2} : Finset (Site 2)) : Set (Site 2)) := by
  apply Set.eq_of_subset_of_subset
  · 
    intro x hx
    have hxminus : x ∈ minusSet (glue (plusField 2) (isoOriginCompletion n)) :=
      minusCluster_subset_minusSet
        (mem_minusSet.mpr (isoOriginCompletion_origin_false n)) hx
    rw [Finset.coe_singleton, Set.mem_singleton_iff]
    by_contra hne
    rw [mem_minusSet, isoOriginCompletion_ne_origin_true n hne] at hxminus
    exact (Bool.noConfusion hxminus)
  · 
    rw [Finset.coe_singleton, Set.singleton_subset_iff]
    exact origin_mem_minusCluster (origin 2)


theorem singletonOrigin_contourEvent_iso (n : ℕ) :
    ContourEvent (↑({origin 2} : Finset (Site 2)) : Set (Site 2)) (bondFinsetTouch 2 n)
      (glue (plusField 2) (isoOriginCompletion n)) := by
  have hev := contourEvent_of_origin_minus (σ := glue (plusField 2) (isoOriginCompletion n)) n
    (isoOriginCompletion_origin_false n)
  rwa [isoOriginCompletion_minusCluster n] at hev


theorem outerContourFill_nonvacuous (n : ℕ) :
    ∃ τ : {x // x ∈ box 2 n} → Bool, glue (plusField 2) τ (origin 2) = false ∧
      (↑({origin 2} : Finset (Site 2)) : Set (Site 2)) ⊆ box 2 n ∧
      IsConnectedCluster ({origin 2} : Finset (Site 2)) ∧
      ContourEvent (↑({origin 2} : Finset (Site 2)) : Set (Site 2)) (bondFinsetTouch 2 n)
        (glue (plusField 2) τ) ∧
      ∃ (T : Finset (Site 2)) (j : ℕ),
        (faceBoundaryGraph (↑({origin 2} : Finset (Site 2)) : Set (Site 2))).support
          ⊆ (T : Set (Site 2)) ∧
        FaceBoundaryConnected (↑({origin 2} : Finset (Site 2)) : Set (Site 2)) T ∧
        j < contourLen (↑({origin 2} : Finset (Site 2)) : Set (Site 2)) (bondFinsetTouch 2 n) ∧
        axisVertex 2 j ∈ T := by
  obtain ⟨hbox, hconn, hsupp, hfbc, hlen, hax⟩ := singletonOrigin_outerContourFill_data n
  exact ⟨isoOriginCompletion n, isoOriginCompletion_origin_false n, hbox, hconn,
    singletonOrigin_contourEvent_iso n, singletonBoundarySupport, 0, hsupp, hfbc, hlen, hax⟩

end Ising
end StatMech
