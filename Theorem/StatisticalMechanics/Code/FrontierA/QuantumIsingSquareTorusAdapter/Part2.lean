/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSquareTorusAdapter.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.AnisotropicSquareTorusKacWard.Part7
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingTrotterCylinder.Part2
import Theorem.StatisticalMechanics.Code.Onsager.TorusIntersection.Part8
import Def.StatisticalMechanics.Code.FrontierA.QuantumIsingSquareTorusAdapter.Part2
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Onsager


theorem squareTorusPositiveEdgeMap_injective
    (L : Nat) [Fact (2 < L)] :
    Function.Injective (squareTorusPositiveEdgeMap L) := by
  rintro ⟨p, mu⟩ ⟨q, nu⟩ h
  have hedge : ons_portEdge L (q, squareTorusPositiveDirection nu) =
      ons_portEdge L (p, squareTorusPositiveDirection mu) :=
    (congrArg Subtype.val h).symm
  rcases (ons_portEdge_eq_iff L
      (p, squareTorusPositiveDirection mu)
      (q, squareTorusPositiveDirection nu)).mp hedge with hsame | hreverse
  · apply Prod.ext
    · exact (congrArg Prod.fst hsame).symm
    · apply Fin.ext
      exact (congrArg (fun d ↦ d.2.val) hsame).symm
  · exfalso
    have hdir := congrArg (fun d ↦ d.2) hreverse
    fin_cases mu <;> fin_cases nu <;> simp [ons_dartRev] at hdir

theorem squareTorusPositiveEdgeMap_surjective
    (L : Nat) [Fact (2 < L)] :
    Function.Surjective (squareTorusPositiveEdgeMap L) := by
  intro edge
  obtain ⟨⟨p, mu⟩, hp⟩ := ons_torusEdge_eq_portEdge L edge.property
  fin_cases mu
  · refine ⟨(p, 0), ?_⟩
    apply Subtype.ext
    exact hp
  · refine ⟨(p, 1), ?_⟩
    apply Subtype.ext
    exact hp
  · refine ⟨((p.1 - 1, p.2), 0), ?_⟩
    apply Subtype.ext
    exact (ons_portEdge_west_eq_horizontal L p).symm.trans hp
  · refine ⟨((p.1, p.2 - 1), 1), ?_⟩
    apply Subtype.ext
    exact (ons_portEdge_south_eq_vertical L p).symm.trans hp


end StatMech.FrontierA
