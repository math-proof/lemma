/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part32
import Mathlib.Analysis.Convex.StrictConvexSpace
import Structure.StatisticalMechanics.Code.FrontierA.KacWardAngularPortGeometry


namespace StatMech.FrontierA

open Set SimpleGraph

open scoped NNReal ENNReal


theorem KWStraightLineEmbedding.exists_angularPortRadiusData
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) :
    Nonempty (KWAngularPortRadiusData embedding) := by
  obtain ⟨rv, hrv, hv⟩ := embedding.exists_uniform_vertex_separation
  obtain ⟨re, hre, he⟩ := embedding.exists_uniform_edge_length
  obtain ⟨rve, hrve, hve⟩ := embedding.exists_uniform_vertex_edge_separation
  let R : ℝ≥0 := min rv (min re rve) / 8
  have hR : 0 < R := by
    dsimp only [R]
    positivity
  refine ⟨⟨R, hR, ?_, ?_, ?_⟩⟩
  · intro v w hvw
    have hle : R ≤ rv / 8 := by
      dsimp only [R]
      gcongr
      exact min_le_left _ _
    have hcast : (R : ℝ) ≤ (rv : ℝ) / 8 := by exact_mod_cast hle
    have := hv v w hvw
    have hrv0 : 0 < (rv : ℝ) := by exact_mod_cast hrv
    linarith
  · intro d
    have hle : R ≤ re / 8 := by
      dsimp only [R]
      gcongr
      exact (min_le_right rv (min re rve)).trans (min_le_left re rve)
    have hcast : (R : ℝ) ≤ (re : ℝ) / 8 := by exact_mod_cast hle
    have := he d
    have hre0 : 0 < (re : ℝ) := by exact_mod_cast hre
    linarith
  · intro v d hvfst hvsnd y hy
    have hle : R ≤ rve / 8 := by
      dsimp only [R]
      gcongr
      exact (min_le_right rv (min re rve)).trans (min_le_right re rve)
    have hcast : (R : ℝ) ≤ (rve : ℝ) / 8 := by exact_mod_cast hle
    have := hve v d hvfst hvsnd y hy
    have hrve0 : 0 < (rve : ℝ) := by exact_mod_cast hrve
    linarith


end StatMech.FrontierA
