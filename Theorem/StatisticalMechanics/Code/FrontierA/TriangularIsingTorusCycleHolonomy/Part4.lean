/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusCycleHolonomy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSurfaceTwist
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveClosure
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusCycleHolonomy.Part4
open scoped BigOperators


namespace StatMech.FrontierA

open scoped Affine


theorem triangularTorusGraphPhase_one_one_apply
    (L : Nat) [Fact (2 < L)] (rho : Complex)
    (d e : (triangularTorusGraph L).Dart) :
    triangularTorusGraphPhase L rho 1 1 d e =
      triangularKacWardTurnMatrix rho
        (triangularTorusGraphDartDirection L d)
        (triangularTorusGraphDartDirection L e) := by
  unfold triangularTorusGraphPhase triangularTorusGraphDartDirection
  simp


theorem triangularTorus_cycleDirection_nonbacktracking
    (L : Nat) [Fact (2 < L)] {root : ZMod L × ZMod L}
    (p : (triangularTorusGraph L).Walk root root) (hp : p.IsCycle) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    forall k,
      triangularTorusGraphDartDirection L (kwGraphCycleDartLoop p (k + 1)) ≠
        triangularTorusDirectionReverse
          (triangularTorusGraphDartDirection L
            (kwGraphCycleDartLoop p k)) := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  intro k hreverse
  let d := (triangularTorusDartEquiv L).symm (kwGraphCycleDartLoop p k)
  let e := (triangularTorusDartEquiv L).symm
    (kwGraphCycleDartLoop p (k + 1))
  have hadj := kwGraphCycleDartLoop_valid p hp k
  have hconsecutive : (triangularTorusDartEquiv L d).snd =
      (triangularTorusDartEquiv L e).fst := by
    simpa [d, e] using hadj
  have hnative :=
    (triangularTorusDartEquiv_consecutive_iff L d e).mp hconsecutive
  have heq : e = triangularTorusDartReverse L d := by
    apply Prod.ext
    · change e.1 = d.1 - triangularTorusDirectionStep L d.2
      rw [eq_sub_iff_add_eq]
      calc
        e.1 + triangularTorusDirectionStep L d.2 =
            triangularTorusDirectionStep L d.2 + e.1 := add_comm _ _
        _ = d.1 := (sub_eq_iff_eq_add.mp hnative).symm
    · exact hreverse
  have hedge : (kwGraphCycleDartLoop p k).edge =
      (kwGraphCycleDartLoop p (k + 1)).edge := by
    rw [show kwGraphCycleDartLoop p k = triangularTorusDartEquiv L d by
          simp [d],
      show kwGraphCycleDartLoop p (k + 1) =
          triangularTorusDartEquiv L e by simp [e],
      heq, triangularTorusDartEquiv_reverse,
      SimpleGraph.Dart.edge_symm]
  exact (kwGraphCycleDartLoop_nonbacktracking
    (triangularTorusGraph L) p hp k).2 hedge


theorem triangularTorus_cyclePhaseProduct_eq_turnProduct
    (L : Nat) [Fact (2 < L)] (rho : Complex)
    {root : ZMod L × ZMod L}
    (p : (triangularTorusGraph L).Walk root root) (hp : p.IsCycle) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    kwLoopPhaseProduct (triangularTorusGraphPhase L rho 1 1)
        (kwGraphCycleDartLoop p) =
      ∏ k, triangularKacWardTurnMatrix rho
        (triangularTorusGraphDartDirection L (kwGraphCycleDartLoop p k))
        (triangularTorusGraphDartDirection L
          (kwGraphCycleDartLoop p (k + 1))) := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  unfold kwLoopPhaseProduct
  apply Finset.prod_congr rfl
  intro k _
  exact triangularTorusGraphPhase_one_one_apply L rho _ _


end StatMech.FrontierA
