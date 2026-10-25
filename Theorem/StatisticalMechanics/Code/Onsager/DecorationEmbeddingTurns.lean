/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbeddingTurns.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationEmbeddingDisjoint
import Def.StatisticalMechanics.Code.Onsager.DecorationEmbeddingTurns


namespace StatMech.Onsager

@[simp] theorem ons_decEdgeMicroDarts_length
    (L : ℕ) (d e : ons_Dart L) :
    (ons_decEdgeMicroDarts L d e).length = 4 := by
  simp [ons_decEdgeMicroDarts]

theorem ons_decEdgeMicroDarts_sites
    (L : ℕ) [Fact (2 < L)] (d e : ons_Dart L)
    (hde : (ons_decGraph L).Adj d e) :
    (ons_decEdgeMicroDarts L d e).map (fun a => a.1) =
      (ons_decEdgeRoute L d e hde).support.dropLast := by
  rw [ons_decEdgeRoute_support]
  simp [ons_decEdgeMicroDarts, ons_decEdgeRouteVertices]

theorem ons_decEdgeMicroDarts_edges
    (L : ℕ) [Fact (2 < L)] (d e : ons_Dart L)
    (hde : (ons_decGraph L).Adj d e) :
    (ons_decEdgeMicroDarts L d e).map (ons_portEdge (8 * L)) =
      (ons_decEdgeRoute L d e hde).edges := by
  letI : Fact (2 < 8 * L) := ⟨by
    have := (Fact.out : 2 < L)
    omega⟩
  simp [ons_decEdgeMicroDarts, ons_portEdge, ons_decEdgeRoute,
    ons_fourDirStepWalk, SimpleGraph.Walk.edges,
    SimpleGraph.Walk.darts]

theorem ons_decEdgeMicroDarts_sum_exponentX_external
    (L : ℕ) [Fact (2 < L)] (d e : ons_Dart L)
    (hrev : e = ons_dartRev L d) :
    ((ons_decEdgeMicroDarts L d e).map
      (fun a => ons_dirExponentX a.2)).sum =
        4 * ons_dirExponentX d.2 := by
  subst e
  rcases d with ⟨p, mu⟩
  fin_cases mu <;>
    simp [ons_decEdgeMicroDarts, ons_decEdgeRouteDirs,
      ons_dartRev, ons_dirExponentX]

theorem ons_decEdgeMicroDarts_sum_exponentY_external
    (L : ℕ) [Fact (2 < L)] (d e : ons_Dart L)
    (hrev : e = ons_dartRev L d) :
    ((ons_decEdgeMicroDarts L d e).map
      (fun a => ons_dirExponentY a.2)).sum =
        4 * ons_dirExponentY d.2 := by
  subst e
  rcases d with ⟨p, mu⟩
  fin_cases mu <;>
    simp [ons_decEdgeMicroDarts, ons_decEdgeRouteDirs,
      ons_dartRev, ons_dirExponentY]

theorem ons_decEdgeMicroDarts_sum_exponentX_internal
    (L : ℕ) [Fact (2 < L)] (d e : ons_Dart L)
    (hint : ons_decInternalAdj d e) :
    ((ons_decEdgeMicroDarts L d e).map
      (fun a => ons_dirExponentX a.2)).sum =
        2 * (ons_dirExponentX e.2 - ons_dirExponentX d.2) := by
  rcases d with ⟨p, mu⟩
  rcases e with ⟨q, nu⟩
  have hpq : p = q := hint.1
  subst q
  fin_cases mu <;> fin_cases nu <;>
    simp [ons_decInternalAdj, ons_decEdgeMicroDarts,
      ons_decEdgeRouteDirs, ons_dartRev, ons_dirStep,
      ons_dirExponentX] at hint ⊢

theorem ons_decEdgeMicroDarts_sum_exponentY_internal
    (L : ℕ) [Fact (2 < L)] (d e : ons_Dart L)
    (hint : ons_decInternalAdj d e) :
    ((ons_decEdgeMicroDarts L d e).map
      (fun a => ons_dirExponentY a.2)).sum =
        2 * (ons_dirExponentY e.2 - ons_dirExponentY d.2) := by
  rcases d with ⟨p, mu⟩
  rcases e with ⟨q, nu⟩
  have hpq : p = q := hint.1
  subst q
  fin_cases mu <;> fin_cases nu <;>
    simp [ons_decInternalAdj, ons_decEdgeMicroDarts,
      ons_decEdgeRouteDirs, ons_dartRev, ons_dirStep,
      ons_dirExponentY] at hint ⊢

@[simp] theorem ons_dirExponentX_dartRev
    (L : ℕ) (d : ons_Dart L) :
    ons_dirExponentX (ons_dartRev L d).2 =
      -ons_dirExponentX d.2 := by
  rcases d with ⟨p, mu⟩
  fin_cases mu <;> simp [ons_dartRev, ons_dirExponentX]

@[simp] theorem ons_dirExponentY_dartRev
    (L : ℕ) (d : ons_Dart L) :
    ons_dirExponentY (ons_dartRev L d).2 =
      -ons_dirExponentY d.2 := by
  rcases d with ⟨p, mu⟩
  fin_cases mu <;> simp [ons_dartRev, ons_dirExponentY]

end StatMech.Onsager
