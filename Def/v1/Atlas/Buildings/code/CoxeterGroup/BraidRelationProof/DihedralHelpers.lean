/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BraidRelationProof/DihedralHelpers.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.Buildings.code.CoxeterGroup.BraidRelation
import Lemma.Real.EqSigma.of.EqBilinForm_E_0
import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.BraidRelationProof.DihedralHelpers
open Finset BigOperators Real


namespace CoxeterGroup

variable {B : Type*} [DecidableEq B] [Fintype B]


/-- The Chebyshev-like sequence $A_n$ that tracks the $e_s$-coefficient of
$(\sigma_s \sigma_t)^n (e_s)$ in the geometric representation. -/
noncomputable def seqA (c α : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => 4 * c ^ 2 - 1
  | (n + 2) => α * seqA c α (n + 1) - seqA c α n

/-- The sequence $B_n$ that tracks the $e_t$-coefficient of
$(\sigma_s \sigma_t)^n (e_s)$. -/
noncomputable def seqB (c α : ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => -2 * c
  | (n + 2) => α * seqB c α (n + 1) - seqB c α n

/-- The sequence $C_n$ that tracks the $e_s$-coefficient of
$(\sigma_s \sigma_t)^n (e_t)$. -/
noncomputable def seqC (c α : ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => 2 * c
  | (n + 2) => α * seqC c α (n + 1) - seqC c α n

/-- The sequence $D_n$ that tracks the $e_t$-coefficient of
$(\sigma_s \sigma_t)^n (e_t)$. -/
noncomputable def seqD (c α : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => -1
  | (n + 2) => α * seqD c α (n + 1) - seqD c α n


end CoxeterGroup
