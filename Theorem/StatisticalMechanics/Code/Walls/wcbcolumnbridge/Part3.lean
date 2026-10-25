/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcbcolumnbridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WindingWitness.Part4
import Theorem.StatisticalMechanics.Code.Walls.wndwinding.Part3
import Theorem.StatisticalMechanics.Code.Walls.wnuupperhalf.Part5
import Theorem.StatisticalMechanics.Code.Walls.wnaalternate.Part3
import Def.StatisticalMechanics.Code.Walls.wcbcolumnbridge.Part3
open Finset Set SimpleGraph
open scoped BigOperators


namespace StatMech

namespace Lattice

theorem wcb_map_snd_filter (L : List ((hypercubicLattice 2).Dart))
    (g : (hypercubicLattice 2).Dart → ℤ) (k : (hypercubicLattice 2).Dart → ℤ) :
    ((L.map (fun d => (k d, g d))).filter (fun p => p.2 ≠ 0)).map Prod.snd =
      (L.map g).filter (fun s => s ≠ 0) := by
  classical
  induction L with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons]
    by_cases ha : g a = 0
    · rw [List.filter_cons_of_neg (by simp [ha]), List.filter_cons_of_neg (by simp [ha]), ih]
    · rw [List.filter_cons_of_pos (by simp [ha]), List.filter_cons_of_pos (by simp [ha]),
        List.map_cons, ih]


theorem wcb_keyedList_snd (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) :
    (wcb_keyedList z w).map Prod.snd = wnu_signedList z w := by
  classical
  unfold wcb_keyedList wnu_signedList
  exact wcb_map_snd_filter w.darts
    (fun d => wnd_signStep z d.toProd.1 d.toProd.2) (fun d => wcb_dartColumn d)


end Lattice
end StatMech
