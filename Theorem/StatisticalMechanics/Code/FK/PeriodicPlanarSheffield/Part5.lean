/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCoverage.Part3
import Theorem.StatisticalMechanics.Code.FK.ContinuousRectangleCrossing.Part9
import Theorem.StatisticalMechanics.Code.Foundations.Ergodicity.Part2
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffield.Part5
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


theorem PeriodicPlaneEmbedding.rectVertices_finite
    (E : PeriodicPlaneEmbedding P) (a b c d : ℝ) :
    (E.rectVertices a b c d).Finite := by
  let lo : Fin 2 → ℝ := fun i => if i = 0 then a else c
  let hi : Fin 2 → ℝ := fun i => if i = 0 then b else d
  let K : Set ℂ := E.coordinates.symm '' Set.Icc lo hi
  have hKcompact : IsCompact K :=
    isCompact_Icc.image E.coordinates.symm.continuous
  obtain ⟨R, hR⟩ := hKcompact.isBounded.subset_closedBall (0 : ℂ)
  apply (E.proper R).subset
  intro x hx
  change a ≤ E.vertexCoord x 0 ∧ E.vertexCoord x 0 ≤ b ∧
    c ≤ E.vertexCoord x 1 ∧ E.vertexCoord x 1 ≤ d at hx
  rcases hx with ⟨hxa, hxb, hxc, hxd⟩
  have hcoord : E.coordinates (E.vertex x) ∈ Set.Icc lo hi := by
    rw [Set.mem_Icc]
    constructor
    · intro i
      fin_cases i
      · simpa [lo, PeriodicPlaneEmbedding.vertexCoord] using hxa
      · simpa [lo, PeriodicPlaneEmbedding.vertexCoord] using hxc
    · intro i
      fin_cases i
      · simpa [hi, PeriodicPlaneEmbedding.vertexCoord] using hxb
      · simpa [hi, PeriodicPlaneEmbedding.vertexCoord] using hxd
  have hvK : (E.vertex x : ℂ) ∈ K := by
    refine ⟨E.coordinates (E.vertex x), hcoord, ?_⟩
    simp
  have hvball := hR hvK
  simpa [Metric.mem_closedBall, dist_zero_left] using hvball

end StatMech.FK.PeriodicPlanar
