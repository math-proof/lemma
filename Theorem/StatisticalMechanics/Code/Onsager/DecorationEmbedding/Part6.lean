/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationEdgeComponent
import Def.StatisticalMechanics.Code.Onsager.DecorationEmbedding.Part7


namespace StatMech.Onsager

theorem ons_decInternalRoute_interior_support
    (L : ℕ) [Fact (2 < L)] (d e : ons_Dart L)
    (hint : ons_decInternalAdj d e) :
    (ons_decEdgeRouteVertices L d e).tail.dropLast =
      (ons_decEdgeInteriorData L d e).map (ons_decMicroVertex L) := by
  rcases d with ⟨p, mu⟩
  rcases e with ⟨q, nu⟩
  have hpq : p = q := hint.1
  subst q
  have hnotrev : (p, nu) ≠ ons_dartRev L (p, mu) := by
    intro h
    have hs := congrArg (fun d : ons_Dart L => d.1) h
    exact ons_dirStep_ne_self L mu p hs.symm
  fin_cases mu <;> fin_cases nu
  all_goals simp [ons_decInternalAdj] at hint
  all_goals
    simp [ons_decEdgeRouteVertices, ons_decEdgeRouteDirs,
      ons_decEdgeInteriorData, ons_decMicroVertex, ons_decEmbedVertex,
      ons_decEmbedOffset, ons_dartRev, ons_dirStep, hnotrev] <;>
    ring_nf <;> simp


end StatMech.Onsager
