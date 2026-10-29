/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CanonicalContour.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.ContourAnchor.Part5
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartInjective
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
import Theorem.StatisticalMechanics.Code.Percolation.PcUpperUncond.Part6
import Def.StatisticalMechanics.Code.Lattice.CanonicalContour.Part4
open Finset Set SimpleGraph Function MeasureTheory
open scoped NNReal ENNReal BigOperators


namespace StatMech

namespace Lattice

open StatMech.Percolation (origin percolationEvent mem_percolationEvent)

variable {ω : ConfigSpace (Sym2 (Site 2))}


theorem mem_closedDartContourEvent_canonical (hfin : (cluster 2 ω (origin 2)).Finite) :
    ω ∈ closedDartContourEvent (ω := ω) hfin := by
  intro D hD
  rw [mem_canonicalContourDarts_iff] at hD
  obtain ⟨k, _, rfl⟩ := hD
  exact orbitDart_primalEdge_isClosed (ω := ω) hfin (k + 1)


theorem closedDartContourEvent_eq_pi (hfin : (cluster 2 ω (origin 2)).Finite) :
    closedDartContourEvent (ω := ω) hfin
      = ((canonicalPrimalEdgeFinset (ω := ω) hfin : Finset (Sym2 (Site 2)))
            : Set (Sym2 (Site 2))).pi (fun _ => ({false} : Set Bool)) := by
  ext η
  simp only [closedDartContourEvent, canonicalPrimalEdgeFinset, Set.mem_setOf_eq, Set.mem_pi,
    List.coe_toFinset, List.mem_map, Set.mem_singleton_iff, forall_exists_index, and_imp]
  constructor
  · rintro h e D hD rfl; exact h D hD
  · intro h D hD; exact h _ D hD rfl


theorem measure_closedDartContourEvent (p : NNReal) (hp : p ≤ 1)
    (hfin : (cluster 2 ω (origin 2)).Finite) :
    (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp) (closedDartContourEvent (ω := ω) hfin)
      = ((1 - p : NNReal) : ENNReal) ^ (canonicalPrimalEdgeFinset (ω := ω) hfin).card := by
  rw [closedDartContourEvent_eq_pi, StatMech.Percolation.cylinder_all_closed]


theorem dartPrimalEdge_injOn_boundaryDarts (K : Set (Site 2)) {e f : Dart}
    (he : IsBoundaryDart K e) (hf : IsBoundaryDart K f)
    (h : dartPrimalEdge e = dartPrimalEdge f) : e = f := by
  rw [dartPrimalEdge_eq, dartPrimalEdge_eq, Sym2.eq_iff] at h
  rcases h with ⟨ht, hh⟩ | ⟨ht, hh⟩
  · exact Dart.ext ht hh
  · 
    
    exact absurd he.1 (by rw [ht]; exact hf.2)


theorem canonicalContourDarts_nodup (hfin : (cluster 2 ω (origin 2)).Finite) :
    (canonicalContourDarts (ω := ω) hfin).Nodup := by
  unfold canonicalContourDarts
  apply List.Nodup.map_on (l := List.range _)
  · intro j hj k hk h
    simp only [List.mem_range] at hj hk
    
    have hpe : dartOrbitPeriod (cluster 2 ω (origin 2))
        ⟨exitDart (ω := ω) hfin, exitDart_isBoundaryDart (ω := ω) hfin⟩
        = Function.minimalPeriod (dartNextSub (cluster 2 ω (origin 2)))
            ⟨exitDart (ω := ω) hfin, exitDart_isBoundaryDart (ω := ω) hfin⟩ := rfl
    have hpos : 0 < Function.minimalPeriod (dartNextSub (cluster 2 ω (origin 2)))
        ⟨exitDart (ω := ω) hfin, exitDart_isBoundaryDart (ω := ω) hfin⟩ :=
      dartOrbitPeriod_pos (cluster 2 ω (origin 2)) hfin _
    
    have hsub : (dartNextSub (cluster 2 ω (origin 2)))^[j + 1]
          ⟨exitDart (ω := ω) hfin, exitDart_isBoundaryDart (ω := ω) hfin⟩
        = (dartNextSub (cluster 2 ω (origin 2)))^[k + 1]
          ⟨exitDart (ω := ω) hfin, exitDart_isBoundaryDart (ω := ω) hfin⟩ := by
      apply Subtype.ext
      rw [dartNextSub_iterate_val, dartNextSub_iterate_val]; exact h
    have := iterate_inj_on_Icc_minimalPeriod (dartNextSub (cluster 2 ω (origin 2)))
      ⟨exitDart (ω := ω) hfin, exitDart_isBoundaryDart (ω := ω) hfin⟩
      (j := j + 1) (k := k + 1) hpos
      (by omega) (by omega) (by omega) (by omega) hsub
    omega
  · exact List.nodup_range


theorem canonicalPrimalEdge_list_nodup (hfin : (cluster 2 ω (origin 2)).Finite) :
    ((canonicalContourDarts (ω := ω) hfin).map dartPrimalEdge).Nodup := by
  apply List.Nodup.map_on _ (canonicalContourDarts_nodup (ω := ω) hfin)
  intro D1 hD1 D2 hD2 heq
  rw [mem_canonicalContourDarts_iff] at hD1 hD2
  obtain ⟨k1, _, rfl⟩ := hD1
  obtain ⟨k2, _, rfl⟩ := hD2
  exact dartPrimalEdge_injOn_boundaryDarts (cluster 2 ω (origin 2))
    (orbitDart_isBoundaryDart (ω := ω) hfin (k1 + 1))
    (orbitDart_isBoundaryDart (ω := ω) hfin (k2 + 1)) heq


theorem canonicalPrimalEdgeFinset_card (hfin : (cluster 2 ω (origin 2)).Finite) :
    (canonicalPrimalEdgeFinset (ω := ω) hfin).card
      = dartOrbitPeriod (cluster 2 ω (origin 2))
          ⟨exitDart (ω := ω) hfin, exitDart_isBoundaryDart (ω := ω) hfin⟩ := by
  unfold canonicalPrimalEdgeFinset
  rw [List.toFinset_card_of_nodup (canonicalPrimalEdge_list_nodup (ω := ω) hfin),
    List.length_map]
  unfold canonicalContourDarts
  rw [List.length_map, List.length_range]


theorem measure_closedDartContourEvent_period (p : NNReal) (hp : p ≤ 1)
    (hfin : (cluster 2 ω (origin 2)).Finite) :
    (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp) (closedDartContourEvent (ω := ω) hfin)
      = ((1 - p : NNReal) : ENNReal) ^ (dartOrbitPeriod (cluster 2 ω (origin 2))
          ⟨exitDart (ω := ω) hfin, exitDart_isBoundaryDart (ω := ω) hfin⟩) := by
  rw [measure_closedDartContourEvent p hp hfin, canonicalPrimalEdgeFinset_card]


end Lattice
end StatMech
