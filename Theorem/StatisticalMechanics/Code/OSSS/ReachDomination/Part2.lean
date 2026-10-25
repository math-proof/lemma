/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/ReachDomination.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.ReachBoxCrossing.Part2
import Def.StatisticalMechanics.Code.OSSS.ReachDomination.Part2
open scoped BigOperators
open MeasureTheory

set_option linter.unusedSectionVars false
set_option linter.style.longLine false


namespace StatMech

namespace OSSS

namespace ReachDomination

open OSSS.Monotonic OSSS.AdaptMConditional StatMech.Probability

open StatMech.OSSS.MonotonicFK

open StatMech.OSSS.AdaptDisintegration

open OSSS.GrandCoupling OSSS.Coding

open StatMech.OSSS.RevealmentBoundAssembly

open StatMech.OSSS.RevealmentBoxCrossing

open StatMech.OSSS.RevealmentConstruction

open StatMech.OSSS.ReachBoxCrossing

open StatMech.Lattice

open scoped Classical

variable {E : Type*} [Fintype E] [DecidableEq E]

variable {V : Type*} [DecidableEq V]


omit [Fintype E] [DecidableEq E] in


theorem clusterMeasurable_indicatorConn (endU endV : E → V) (B C : Set V) :
    ClusterMeasurable (indicatorConn endU endV B C) endU endV B := by
  intro X w hagree
  unfold indicatorConn
  by_cases hX : ∃ x ∈ C, ConnOpenSet endU endV X x B
  · obtain ⟨x, hxC, hconn⟩ := hX
    have hw : ∃ x ∈ C, ConnOpenSet endU endV w x B :=
      ⟨x, hxC, connOpenSet_stable_of_agree hagree hconn⟩
    rw [if_pos hw, if_pos ⟨x, hxC, hconn⟩]
  · have hw : ¬ ∃ x ∈ C, ConnOpenSet endU endV w x B := by
      rintro ⟨x, hxC, hconn⟩
      exact hX ⟨x, hxC, (connOpenSet_iff_of_agree hagree).mp hconn⟩
    rw [if_neg hw, if_neg hX]


end ReachDomination
end OSSS
end StatMech
