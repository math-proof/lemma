module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPerron.Part9
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexParticleHole.Part4
open Finset Matrix


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexParticleHole.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable def sixVertexLambdaNeg (N r : ℕ) (hN : Even N)
    (hr : r ≤ N / 2) (c : ℝ) : ℝ :=
  sixVertexSectorTopEigenvalue N (N / 2 + r) (sixVertex_half_add_le hN hr) c

end StatMech.FrontierD
