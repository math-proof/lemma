/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneTrifurcation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarBurtonKeaneMerge.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.FiniteCutHubCount
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarBurtonKeaneTrifurcation
open Filter MeasureTheory Set SimpleGraph Topology Finset
open scoped ENNReal BigOperators


namespace StatMech.FK.PeriodicPlanar

open Lattice StatMech.FrontierA

variable {V : Type*} [Countable V] [DecidableEq V]


theorem measurable_removeVertex (x : V) :
    Measurable (removeVertex x :
      ConfigSpace (Sym2 V) -> ConfigSpace (Sym2 V)) := by
  apply measurable_pi_lambda
  intro e
  by_cases hx : x ∈ e
  · simpa [removeVertex, hx] using
      (measurable_const : Measurable (fun _ : ConfigSpace (Sym2 V) => false))
  · simpa [removeVertex, hx] using ConfigSpace.measurable_eval e

theorem PeriodicGraph.removeVertex_configTranslate
    (P : PeriodicGraph V) (z : Site 2)
    (omega : ConfigSpace (Sym2 V)) (x : V) :
    removeVertex (P.shift z x) (P.configTranslate z omega) =
      P.configTranslate z (removeVertex x omega) := by
  funext e
  induction e using Sym2.inductionOn with
  | _ a b =>
      simp only [removeVertex, PeriodicGraph.configTranslate, Sym2.map_mk]
      have hmem : P.shift z x ∈ s(a, b) ↔
          x ∈ s(P.shift (-z) a, P.shift (-z) b) := by
        simp only [Sym2.mem_iff]
        constructor
        · rintro (h | h)
          · left
            simpa only [h] using (P.shift_neg_shift z x).symm
          · right
            simpa only [h] using (P.shift_neg_shift z x).symm
        · rintro (h | h)
          · left
            calc
              P.shift z x = P.shift z (P.shift (-z) a) := congrArg (P.shift z) h
              _ = a := P.shift_shift_neg z a
          · right
            calc
              P.shift z x = P.shift z (P.shift (-z) b) := congrArg (P.shift z) h
              _ = b := P.shift_shift_neg z b
      by_cases hx : P.shift z x ∈ s(a, b)
      · rw [if_pos hx, if_pos (hmem.mp hx)]
      · rw [if_neg hx, if_neg (fun h => hx (hmem.mpr h))]


end StatMech.FK.PeriodicPlanar
