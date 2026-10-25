/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionCurrentLimits.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.BoundaryCurrentTail.Part2
import Theorem.StatisticalMechanics.Code.FrontierB.InfiniteCurrentFiniteMarginals
import Theorem.StatisticalMechanics.Code.FrontierB.InfiniteCurrentCompactness
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Def.StatisticalMechanics.Code.FrontierB.GeneralInteractionCurrentLimits.Part2
open Filter MeasureTheory Set Topology
open scoped ENNReal


namespace StatMech.FrontierB

open Sharpness Lattice


theorem SummableFerromagneticInteraction.row_comp_addLeft {d : Nat}
    (I : SummableFerromagneticInteraction d) (x : Site d) :
    (fun y => I.coupling s(x, y)) ∘ Equiv.addLeft x =
      fun y => I.coupling s((0 : Site d), y) := by
  funext y
  change I.coupling s(x, x + y) = I.coupling s(0, y)
  simpa using I.translation_invariant x (0 : Site d) y


theorem SummableFerromagneticInteraction.row_summable {d : Nat}
    (I : SummableFerromagneticInteraction d) (x : Site d) :
    Summable (fun y => I.coupling s(x, y)) := by
  apply (Equiv.addLeft x).summable_iff.mp
  simpa only [I.row_comp_addLeft x] using I.summable_origin


theorem SummableFerromagneticInteraction.row_tsum_eq_strength {d : Nat}
    (I : SummableFerromagneticInteraction d) (x : Site d) :
    (∑' y, I.coupling s(x, y)) = I.strength := by
  calc
    (∑' y, I.coupling s(x, y)) =
        ∑' y, I.coupling s(x, Equiv.addLeft x y) :=
      (Equiv.tsum_eq (Equiv.addLeft x)
        (fun y => I.coupling s(x, y))).symm
    _ = I.strength := by
      apply tsum_congr
      intro y
      exact congrFun (I.row_comp_addLeft x) y

theorem SummableFerromagneticInteraction.strength_nonneg {d : Nat}
    (I : SummableFerromagneticInteraction d) : 0 <= I.strength := by
  exact tsum_nonneg fun y => I.nonneg _


theorem SummableFerromagneticInteraction.coupling_le_strength {d : Nat}
    (I : SummableFerromagneticInteraction d) (e : Sym2 (Site d)) :
    I.coupling e <= I.strength := by
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [← I.row_tsum_eq_strength x]
      exact (I.row_summable x).le_tsum y (fun z _ => I.nonneg s(x, z))


end StatMech.FrontierB
