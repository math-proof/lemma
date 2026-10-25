/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingEarInduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
import Theorem.StatisticalMechanics.Code.Lattice.TurningNumber.Part6
import Theorem.StatisticalMechanics.Code.Lattice.OrbitEncloses.Part4
import Theorem.StatisticalMechanics.Code.Lattice.JordanSingleCycle.Part4
import Theorem.StatisticalMechanics.Code.Lattice.MinimalPeriodLoop.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.OrbitExteriorEven
import Theorem.StatisticalMechanics.Code.Lattice.OrbitInteriorOdd
import Theorem.StatisticalMechanics.Code.Lattice.ClosedContourSeparation.Part2
import Theorem.StatisticalMechanics.Code.Lattice.BdEdgeMatchStarHull
import Theorem.StatisticalMechanics.Code.Lattice.CornerBalance.Part4
import Theorem.StatisticalMechanics.Code.Lattice.EarRemoval.Part5
import Theorem.StatisticalMechanics.Code.Lattice.EarExistence.Part4
import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
import Theorem.StatisticalMechanics.Code.Lattice.BalancePreservingContraction.Part4
import Theorem.StatisticalMechanics.Code.Lattice.JordanSeparationFull
import Theorem.StatisticalMechanics.Code.Lattice.NoDiagTouchClose.Part4
import Def.StatisticalMechanics.Code.Lattice.WindingEarInduction
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

theorem wei_windingWitness_transfer_diff_singleton (K : Set (Site 2)) (c : Site 2)
    (a : {e : Dart // IsBoundaryDart K e}) (a' : {e : Dart // IsBoundaryDart (K \ {c}) e})
    (hval : a'.1 = a.1)
    (hnp : ∀ i, bpc_NotProbed c ((dartNext K)^[i] a.1))
    (hw : wei_WindingWitness (K \ {c}) a') :
    wei_WindingWitness K a := by
  obtain ⟨z, hzK', hzodd⟩ := hw
  refine ⟨z, ((Set.mem_diff _).mp hzK').1, ?_⟩
  rwa [wei_rayCount_diff_singleton K c a a' hval hnp z] at hzodd


theorem wei_dartFace_trans (w : Site 2) (e : Dart) :
    dartFace (transDart w e) = dartFace e + w := by
  unfold dartFace
  rw [transDart_tail, transDart_dir]
  funext i
  fin_cases i
  · show e.tail 0 + w 0 + negPart (e.dir 0) + negPart (rot90Fun e.dir 0)
      = (e.tail 0 + negPart (e.dir 0) + negPart (rot90Fun e.dir 0)) + w 0
    ring
  · show e.tail 1 + w 1 + negPart (e.dir 1) + negPart (rot90Fun e.dir 1)
      = (e.tail 1 + negPart (e.dir 1) + negPart (rot90Fun e.dir 1)) + w 1
    ring


theorem wei_rayEdge_trans (w z x y : Site 2) :
    jec_rayEdge (z + w) s(x + w, y + w) ↔ jec_rayEdge z s(x, y) := by
  rw [jec_rayEdge_mk, jec_rayEdge_mk]; simp only [Pi.add_apply]; omega


theorem wei_rayCount_trans (K : Set (Site 2)) (w : Site 2)
    (a : {e : Dart // IsBoundaryDart K e}) (z : Site 2) :
    jec_rayCount (z + w) (mpl_orbitLoop (transSet w K) (transSub K w a))
      = jec_rayCount z (mpl_orbitLoop K a) := by
  classical
  rw [jec_rayCount, jec_rayCount, wei_mpl_orbitLoop_edges_eq, wei_mpl_orbitLoop_edges_eq]
  rw [transSub_val, dartOrbitPeriod_trans]
  have hmap : (List.range (dartOrbitPeriod K a)).map
        (fun k => s(dartFace ((dartNext (transSet w K))^[k] (transDart w a.1)),
          dartFace ((dartNext (transSet w K))^[k + 1] (transDart w a.1))))
      = (List.range (dartOrbitPeriod K a)).map
        (fun k => s(dartFace ((dartNext K)^[k] a.1) + w,
          dartFace ((dartNext K)^[k + 1] a.1) + w)) := by
    apply List.map_congr_left
    intro k _
    rw [iterate_dartNext_trans, iterate_dartNext_trans, wei_dartFace_trans, wei_dartFace_trans]
  rw [hmap, List.countP_map, List.countP_map]
  apply List.countP_congr
  intro k _
  simp only [Function.comp_apply, decide_eq_true_eq]
  exact wei_rayEdge_trans w z _ _


theorem wei_ucBase1_edges :
    (mpl_orbitLoop unitCell ucBase1).edges
      = [s((![0, -1] : Site 2), ![-1, -1]), s((![-1, -1] : Site 2), ![-1, 0]),
          s((![-1, 0] : Site 2), ![0, 0]), s((![0, 0] : Site 2), ![0, -1])] := by
  rw [wei_mpl_orbitLoop_edges_eq, ucBase1_orbitPeriod]
  show ((List.range 4).map (fun k => s(dartFace ((dartNext unitCell)^[k] ucDart1),
      dartFace ((dartNext unitCell)^[k + 1] ucDart1)))) = _
  rw [show (List.range 4) = [0, 1, 2, 3] from rfl]
  simp only [List.map_cons, List.map_nil]
  rw [show ((dartNext unitCell)^[0] ucDart1) = ucDart1 from rfl, it1_1, it1_2, it1_3, it1_4]
  rw [mpl_dartFace_ucDart1, mpl_dartFace_ucDart2, mpl_dartFace_ucDart3, mpl_dartFace_ucDart0]


theorem wei_ucBase2_edges :
    (mpl_orbitLoop unitCell ucBase2).edges
      = [s((![-1, -1] : Site 2), ![-1, 0]), s((![-1, 0] : Site 2), ![0, 0]),
          s((![0, 0] : Site 2), ![0, -1]), s((![0, -1] : Site 2), ![-1, -1])] := by
  rw [wei_mpl_orbitLoop_edges_eq, ucBase2_orbitPeriod]
  show ((List.range 4).map (fun k => s(dartFace ((dartNext unitCell)^[k] ucDart2),
      dartFace ((dartNext unitCell)^[k + 1] ucDart2)))) = _
  rw [show (List.range 4) = [0, 1, 2, 3] from rfl]
  simp only [List.map_cons, List.map_nil]
  rw [show ((dartNext unitCell)^[0] ucDart2) = ucDart2 from rfl, it2_1, it2_2, it2_3, it2_4]
  rw [mpl_dartFace_ucDart2, mpl_dartFace_ucDart3, mpl_dartFace_ucDart0, mpl_dartFace_ucDart1]


theorem wei_ucBase3_edges :
    (mpl_orbitLoop unitCell ucBase3).edges
      = [s((![-1, 0] : Site 2), ![0, 0]), s((![0, 0] : Site 2), ![0, -1]),
          s((![0, -1] : Site 2), ![-1, -1]), s((![-1, -1] : Site 2), ![-1, 0])] := by
  rw [wei_mpl_orbitLoop_edges_eq, ucBase3_orbitPeriod]
  show ((List.range 4).map (fun k => s(dartFace ((dartNext unitCell)^[k] ucDart3),
      dartFace ((dartNext unitCell)^[k + 1] ucDart3)))) = _
  rw [show (List.range 4) = [0, 1, 2, 3] from rfl]
  simp only [List.map_cons, List.map_nil]
  rw [show ((dartNext unitCell)^[0] ucDart3) = ucDart3 from rfl, it3_1, it3_2, it3_3, it3_4]
  rw [mpl_dartFace_ucDart3, mpl_dartFace_ucDart0, mpl_dartFace_ucDart1, mpl_dartFace_ucDart2]


theorem wei_unitCell_basepoint_rayCount (b : {e : Dart // IsBoundaryDart unitCell e})
    (hb : b.1 = ucDart0 ∨ b.1 = ucDart1 ∨ b.1 = ucDart2 ∨ b.1 = ucDart3) :
    jec_rayCount (![0, 0] : Site 2) (mpl_orbitLoop unitCell b) = 1 := by
  rcases hb with h | h | h | h
  · have hb0 : b = ucBase := Subtype.ext h
    rw [hb0]; exact mpl_unitCell_rayCount_eq_one
  · have hb1 : b = ucBase1 := Subtype.ext h
    rw [hb1, wei_rayCount_of_perm (mpl_orbitLoop unitCell ucBase1) (mpl_orbitLoop unitCell ucBase)
        (![0, 0] : Site 2) ?_]
    · exact mpl_unitCell_rayCount_eq_one
    · rw [wei_ucBase1_edges, jsf_unitCell_loop_edges]; decide
  · have hb2 : b = ucBase2 := Subtype.ext h
    rw [hb2, wei_rayCount_of_perm (mpl_orbitLoop unitCell ucBase2) (mpl_orbitLoop unitCell ucBase)
        (![0, 0] : Site 2) ?_]
    · exact mpl_unitCell_rayCount_eq_one
    · rw [wei_ucBase2_edges, jsf_unitCell_loop_edges]; decide
  · have hb3 : b = ucBase3 := Subtype.ext h
    rw [hb3, wei_rayCount_of_perm (mpl_orbitLoop unitCell ucBase3) (mpl_orbitLoop unitCell ucBase)
        (![0, 0] : Site 2) ?_]
    · exact mpl_unitCell_rayCount_eq_one
    · rw [wei_ucBase3_edges, jsf_unitCell_loop_edges]; decide


theorem wei_singleton_windingWitness (v : Site 2)
    (a : {e : Dart // IsBoundaryDart ({v} : Set (Site 2)) e}) :
    wei_WindingWitness ({v} : Set (Site 2)) a := by
  refine ⟨v, Set.mem_singleton _, ?_⟩
  
  obtain ⟨b, hbU, hval⟩ : ∃ b : {e : Dart // IsBoundaryDart unitCell e},
      (b.1 = ucDart0 ∨ b.1 = ucDart1 ∨ b.1 = ucDart2 ∨ b.1 = ucDart3) ∧
        a.1 = transDart v b.1 := by
    rcases singleton_boundaryDart_eq_transDart v a.1 a.2 with
      ⟨he, _⟩ | ⟨he, _⟩ | ⟨he, _⟩ | ⟨he, _⟩
    · exact ⟨ucBase, Or.inl rfl, he⟩
    · exact ⟨ucBase2, Or.inr (Or.inr (Or.inl rfl)), he⟩
    · exact ⟨ucBase3, Or.inr (Or.inr (Or.inr rfl)), he⟩
    · exact ⟨ucBase1, Or.inr (Or.inl rfl), he⟩
  
  have hset : ({v} : Set (Site 2)) = transSet v unitCell := (transSet_unitCell v).symm
  
  have hcongr : jec_rayCount v (mpl_orbitLoop ({v} : Set (Site 2)) a)
      = jec_rayCount v (mpl_orbitLoop (transSet v unitCell) (transSub unitCell v b)) := by
    apply wei_rayCount_congr ({v} : Set (Site 2)) (transSet v unitCell) hset
    rw [hval, transSub_val]
  rw [hcongr]
  
  have hv0 : ((![0, 0] : Site 2) + v) = v := by funext i; fin_cases i <;> simp
  have htrans := wei_rayCount_trans unitCell v b (![0, 0] : Site 2)
  rw [hv0] at htrans
  rw [htrans, wei_unitCell_basepoint_rayCount b hbU]
  decide


end Lattice
end StatMech
