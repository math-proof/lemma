/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerron.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertex.Part9
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPerron.Part6
open Finset Matrix


namespace StatMech.FrontierD

noncomputable def sixVertexConnectionExponent {N n : ℕ} (hn : n ≤ N)
    {c : ℝ} (hc : 0 < c) (x y : SixVertexSector N n) : ℕ :=
  Classical.choose ((Matrix.isIrreducible_iff_exists_pow_pos
    (sixVertexSectorTransfer_nonneg hc.le)).mp
      (sixVertexSectorTransfer_isIrreducible hn hc) x y)

end StatMech.FrontierD
