/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Problem_2_4.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
open Finset BigOperators Real


/-- `a` is the (nonnegative) decreasing rearrangement of `|θ|`: it has the same
multiset of values as `|θ_i|`, is nonnegative, and is antitone. -/
structure IsDecreasingRearrangement {d : ℕ} (θ : Fin d → ℝ) (a : Fin d → ℝ) : Prop where
  nonneg : ∀ j, 0 ≤ a j
  antitone : Antitone a
  multiset_eq : Multiset.map a Finset.univ.val = Multiset.map (fun i => |θ i|) Finset.univ.val

