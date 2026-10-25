/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionPrismGinibre.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionBoxPrismEnergy.Part5
import Theorem.StatisticalMechanics.Code.Ising.GinibreBoundaryDerivativeLower
import Theorem.StatisticalMechanics.Code.Ising.PlusStateSpinProfileLimit
import Theorem.StatisticalMechanics.Code.IsingFK.MagnetizationFK
import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionPrismGinibre
open scoped BigOperators
open Finset
open MeasureTheory


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness StatMech.Lattice

noncomputable section

theorem oddPrismTouchToInternal_toTouch (n : Nat)
    (q : OddPrismInternalIndex n) :
    oddPrismTouchToInternal n (oddPrismInternalIndexToTouch n q) = some q := by
  rcases q with q | q
  · rfl
  · rcases q with q | q <;> rfl

theorem oddPrismInternalIndexToTouch_injective (n : Nat) :
    Function.Injective (oddPrismInternalIndexToTouch n) := by
  intro q r h
  have hm := congrArg (oddPrismTouchToInternal n) h
  rw [oddPrismTouchToInternal_toTouch,
    oddPrismTouchToInternal_toTouch] at hm
  exact Option.some.inj hm

theorem oddPrismInternalEdge_map_eq_touch (n : Nat)
    (q : OddPrismInternalIndex n) :
    Sym2.map
        (fun v => (rectangularPrismSiteEquivSctBoxDobrushin n v).1)
        (oddPrismInternalEdge n q) =
      oddPrismTouchIndexBond n (oddPrismInternalIndexToTouch n q) := by
  rcases q with q | q
  · rw [oddPrismInternalEdge, Sym2.map_pair_eq]
    rfl
  · rcases q with q | q
    · rw [oddPrismInternalEdge, Sym2.map_pair_eq]
      rfl
    · rw [oddPrismInternalEdge, Sym2.map_pair_eq]
      rfl

theorem oddPrismInternalEdge_injective (n : Nat) :
    Function.Injective (oddPrismInternalEdge n) := by
  intro q r h
  have hm := congrArg
    (Sym2.map
      (fun v => (rectangularPrismSiteEquivSctBoxDobrushin n v).1)) h
  rw [oddPrismInternalEdge_map_eq_touch,
    oddPrismInternalEdge_map_eq_touch] at hm
  exact oddPrismInternalIndexToTouch_injective n
    (oddPrismTouchIndexBond_injective n hm)


end
end StatMech.FrontierA
