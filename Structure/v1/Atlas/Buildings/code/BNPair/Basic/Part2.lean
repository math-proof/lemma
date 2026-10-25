/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/Basic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.GroupTheory.Coxeter.Length
import Def.v1.Atlas.Buildings.code.BNPair.Basic
set_option linter.unusedSectionVars false


/-- The defining axioms of a Tits system: multiplication rules
$C(w) \cdot C(s) \subseteq C(ws)$ when $\ell(ws) > \ell(w)$, and
$C(w) \cdot C(s) \subseteq C(ws) \cup C(w)$ otherwise, together with the
non-normality condition $\exists b \in B, nbn^{-1} \notin B$ for each lift $n$ of a simple $s$. -/
structure BNPairAxioms {G : Type*} [Group G] {B_idx : Type*}
    {M : CoxeterMatrix B_idx} (bp : BNPair G M) where
  cell_mul_length_increasing : ∀ (w : M.Group) (s : B_idx),
    M.toCoxeterSystem.length (w * M.toCoxeterSystem.simple s) >
      M.toCoxeterSystem.length w →
    setMul (bp.bruhatCell w) (bp.bruhatCell (M.toCoxeterSystem.simple s)) ⊆
      bp.bruhatCell (w * M.toCoxeterSystem.simple s)
  cell_mul_length_decreasing : ∀ (w : M.Group) (s : B_idx),
    M.toCoxeterSystem.length (w * M.toCoxeterSystem.simple s) <
      M.toCoxeterSystem.length w →
    setMul (bp.bruhatCell w) (bp.bruhatCell (M.toCoxeterSystem.simple s)) ⊆
      bp.bruhatCell (w * M.toCoxeterSystem.simple s) ∪ bp.bruhatCell w
  conjugate_not_sub : ∀ (s : B_idx) (n : bp.N),
    bp.π n = M.toCoxeterSystem.simple s →
    ∃ b : bp.B, (n : G) * b * (n : G)⁻¹ ∉ bp.B

