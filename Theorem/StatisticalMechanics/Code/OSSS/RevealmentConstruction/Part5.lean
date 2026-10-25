/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentConstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.Revealment.Part2
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Def.StatisticalMechanics.Code.OSSS.RevealmentConstruction.Part4
open scoped BigOperators
open Finset
open StatMech.Lattice

set_option linter.style.longLine false


namespace StatMech

namespace OSSS

namespace RevealmentConstruction

open StatMech.OSSS

open StatMech.OSSS.DecisionTree

open StatMech.OSSS.Revealment

open scoped Classical

variable {E : Type*} [Fintype E] [DecidableEq E]


variable {V : Type*} [DecidableEq V]


omit [Fintype E] [DecidableEq E] in


theorem geomInv_step (endU endV : E → V) (ω : ConfigSpace E) (B : Set V)
    (disc : Finset V) (e : E) (hInv : geomInv endU endV ω B disc)
    (hg : geomGuard endU endV disc e = true) :
    geomInv endU endV ω B (geomStep endU endV disc e (ω e)) := by
  unfold geomGuard at hg; simp only [decide_eq_true_eq] at hg
  unfold geomStep
  by_cases hb : ω e = true
  · rw [if_pos hb]
    have hUc : ConnOpenSet endU endV ω (endU e) B := by
      rcases hg with hU | hV
      · exact hInv _ hU
      · exact connOpenSet_prop' hb (hInv _ hV)
    have hVc : ConnOpenSet endU endV ω (endV e) B := connOpenSet_prop hb hUc
    intro x hx
    rw [Finset.mem_insert, Finset.mem_insert] at hx
    rcases hx with rfl | rfl | hx
    · exact hUc
    · exact hVc
    · exact hInv x hx
  · simp only [Bool.not_eq_true] at hb; rw [hb]; simpa using hInv


end RevealmentConstruction
end OSSS
end StatMech
