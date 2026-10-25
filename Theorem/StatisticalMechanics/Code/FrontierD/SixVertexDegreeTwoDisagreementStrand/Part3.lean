/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoDisagreementStrand.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDisagreementComponentCType.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopTopology.Part4
import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusMedial.Part5
import Mathlib.Algebra.Group.End
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.Perm.Cycle.Factors
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part4
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexTorusDartBondMate_involutive
    (T : EvenTorus) (d : SixVertexTorusDart T) :
    sixVertexTorusDartBondMate T (sixVertexTorusDartBondMate T d) = d := by
  rcases d with ⟨⟨i, j⟩, side⟩
  fin_cases side <;>
    simp [sixVertexTorusDartBondMate, finitePeriodicSucc_cyclicPred,
      svCyclicPred_finitePeriodicSucc]

theorem EvenTorus.one_lt_width (T : EvenTorus) : 1 < T.width := by
  obtain ⟨k, hk⟩ := T.width_even
  have hpos := T.width_pos
  rw [hk] at hpos ⊢
  omega

theorem EvenTorus.one_lt_height (T : EvenTorus) : 1 < T.height := by
  obtain ⟨k, hk⟩ := T.height_even
  have hpos := T.height_pos
  rw [hk] at hpos ⊢
  omega

theorem sixVertexTorusDartBondMate_vertex_ne
    (T : EvenTorus) (d : SixVertexTorusDart T) :
    (sixVertexTorusDartBondMate T d).1 ≠ d.1 := by
  rcases d with ⟨⟨i, j⟩, side⟩
  fin_cases side
  · intro h
    exact cyclicPred_ne_self T.one_lt_width i
      (congrArg Prod.fst h)
  · intro h
    exact finitePeriodicSucc_ne_self T.one_lt_width i
      (congrArg Prod.fst h)
  · intro h
    exact cyclicPred_ne_self T.one_lt_height j
      (congrArg Prod.snd h)
  · intro h
    exact finitePeriodicSucc_ne_self T.one_lt_height j
      (congrArg Prod.snd h)

theorem sixVertexTorusDartEdge_bondMate
    (T : EvenTorus) (d : SixVertexTorusDart T) :
    sixVertexTorusDartEdge T (sixVertexTorusDartBondMate T d) =
      sixVertexTorusDartEdge T d := by
  rcases d with ⟨⟨i, j⟩, side⟩
  fin_cases side <;>
    simp [sixVertexTorusDartBondMate, sixVertexTorusDartEdge,
      sixVertexTorusIncidentEdge, svCyclicPred_finitePeriodicSucc]


end
end StatMech.FrontierD
