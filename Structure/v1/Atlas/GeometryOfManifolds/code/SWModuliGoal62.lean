/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/SWModuliGoal62.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.FourManifoldsSW.Part8
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.FourManifoldsSW
import Def.v1.Atlas.GeometryOfManifolds.code.SWModuliGoal62.Part2
set_option autoImplicit false


/-- Definition 2: a smooth-manifold structure on the SW moduli space $\mathcal{M}(S, g, \mu) = \{\text{SW solutions}\}/\mathcal{G}$, with the quotient projection identifying gauge orbits with points. -/
structure SWModuliSmoothManifold
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ⊤ M]
    [CompactSpace M]
    {Ω1 Ω2 : Type*} [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]
    (spinc : SpinCStructure M Ω1 Ω2)
    [htop : Has4ManifoldTopology M]
    [IsGenericPair spinc] where
  dimension : ℕ
  carrier : Type
  topologicalSpace : TopologicalSpace carrier
  chartedSpace : @ChartedSpace (EuclideanSpace ℝ (Fin dimension)) _ carrier topologicalSpace
  isManifold : letI := topologicalSpace; letI := chartedSpace;
    IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin dimension))) ⊤ carrier
  orientable : letI := topologicalSpace; letI := chartedSpace;
    IsOrientableManifold dimension carrier
  gauge : GaugeActionData spinc
  quotientProj : SWSolution spinc → carrier
  proj_identifies_orbits : ∀ (sol₁ sol₂ : SWSolution spinc),
    SWGaugeEquivalent gauge sol₁ sol₂ → quotientProj sol₁ = quotientProj sol₂
  proj_injective : ∀ (sol₁ sol₂ : SWSolution spinc),
    quotientProj sol₁ = quotientProj sol₂ → SWGaugeEquivalent gauge sol₁ sol₂

/-- The SW moduli space packaged as a compact smooth manifold (smooth manifold structure plus compactness). -/
structure SWModuliManifold
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ⊤ M]
    [CompactSpace M]
    {Ω1 Ω2 : Type*} [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]
    (spinc : SpinCStructure M Ω1 Ω2)
    [htop : Has4ManifoldTopology M]
    [IsGenericPair spinc] where
  smooth : SWModuliSmoothManifold spinc
  compactSpace : letI := smooth.topologicalSpace; CompactSpace smooth.carrier

