/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Problem_2_4.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Structure.v1.Atlas.HighDimensionalStatistics.code.Chapter2.Problem_2_4
open Finset BigOperators Real


/-- Weak `ℓ_q` norm of a rearranged vector `a`: `max_j (j+1)^{1/q} · a_j`. -/
noncomputable def weakLqNorm {d : ℕ} [NeZero d] (q : ℝ) (a : Fin d → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun j : Fin d => ((j.val + 1 : ℝ) ^ (1 / q)) * a j)

/-- Strong (standard) `ℓ_q` norm of `θ`: `(∑_i |θ_i|^q)^{1/q}`. -/
noncomputable def strongLqNorm {d : ℕ} (q : ℝ) (θ : Fin d → ℝ) : ℝ :=
  (∑ i : Fin d, |θ i| ^ q) ^ (1 / q)

/-- Membership in the weak `ℓ_q` ball of radius `R`: `a_j ≤ R · (j+1)^{-1/q}` for all `j`. -/
def InWeakLqBall {d : ℕ} (a : Fin d → ℝ) (q R : ℝ) : Prop :=
  ∀ j : Fin d, a j ≤ R * ((j.val + 1 : ℝ) ^ (-(1 / q)))

