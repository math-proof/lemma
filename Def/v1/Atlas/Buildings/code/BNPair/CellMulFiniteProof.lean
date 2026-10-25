/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/CellMulFiniteProof.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.Buildings.code.BNPair.Basic.Part2
import Mathlib.Tactic.Group
import Theorem.v1.Atlas.Buildings.code.BNPair.CellMulFiniteProof
set_option linter.unusedSectionVars false

open scoped Classical

variable {G : Type*} [Group G] {B_idx : Type*} {M : CoxeterMatrix B_idx}


namespace CellMulFinite

open BNPair

/-- The (at most two-element) finset $\{ws, w\}$ covering $C(w) \cdot C(s)$ in the union of cells. -/
noncomputable def setMul_bruhatCell_simple_finset (_bp : BNPair G M) (_ax : BNPairAxioms _bp)
    (w : M.Group) (s : B_idx) : Finset M.Group :=
  {w * M.toCoxeterSystem.simple s, w}

end CellMulFinite
