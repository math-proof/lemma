/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/SWModuliGoal62.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.FourManifoldsSW.Part8
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.FourManifoldsSW
import Def.v1.Atlas.GeometryOfManifolds.code.SWModuliGoal62
set_option autoImplicit false


/-- A generic pair $(g, \mu)$ ensures that the Seiberg–Witten linearization is surjective at irreducible solutions, the cokernel dimension is zero, and the Fredholm index equals $\tfrac{1}{4}(c_1(L)^2 \cdot [X] - (2\chi + 3\sigma))$. -/
class IsGenericPair
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ⊤ M]
    [CompactSpace M]
    {Ω1 Ω2 : Type*} [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]
    [htop : Has4ManifoldTopology M]
    (spinc : SpinCStructure M Ω1 Ω2) where
  cokerDim : SWSolution spinc → ℕ
  fredholmIndex : SWSolution spinc → ℤ
  fredholmIndex_eq : ∀ (sol : SWSolution spinc),
    fredholmIndex sol * 4 = spinc.c₁_L - (2 * htop.euler + 3 * htop.Q.signature)
  linearised_surjective : ∀ (sol : SWSolution spinc), ¬sol.isReducible → cokerDim sol = 0
  no_reducible_solutions : htop.Q.b₂_plus ≥ 1 → ∀ (sol : SWSolution spinc), ¬sol.isReducible


