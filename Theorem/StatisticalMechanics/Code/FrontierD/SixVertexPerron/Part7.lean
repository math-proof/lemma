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
import Def.StatisticalMechanics.Code.FrontierD.SixVertexPerron.Part6
open Finset Matrix


namespace StatMech.FrontierD

theorem sixVertexConnectionExponent_pos {N n : ℕ} (hn : n ≤ N)
    {c : ℝ} (hc : 0 < c) (x y : SixVertexSector N n) :
    0 < sixVertexConnectionExponent hn hc x y :=
  (Classical.choose_spec ((Matrix.isIrreducible_iff_exists_pow_pos
    (sixVertexSectorTransfer_nonneg hc.le)).mp
      (sixVertexSectorTransfer_isIrreducible hn hc) x y)).1

theorem sixVertexConnectionExponent_entry_pos {N n : ℕ} (hn : n ≤ N)
    {c : ℝ} (hc : 0 < c) (x y : SixVertexSector N n) :
    0 < (sixVertexSectorTransfer N n c ^ sixVertexConnectionExponent hn hc x y) x y :=
  (Classical.choose_spec ((Matrix.isIrreducible_iff_exists_pow_pos
    (sixVertexSectorTransfer_nonneg hc.le)).mp
      (sixVertexSectorTransfer_isIrreducible hn hc) x y)).2


end StatMech.FrontierD
