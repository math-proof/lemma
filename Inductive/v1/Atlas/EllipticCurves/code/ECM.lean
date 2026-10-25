/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ECM.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.EllipticCurves.code.IntegerFactorization.Part4
import Lemma.Complex.Atlas.v1.EllipticCurves.code.IntegerFactorization
import Def.v1.Atlas.EllipticCurves.code.ECM.Part2


noncomputable section

open Nat Finset

/-- The outcome of one trial of ECM (Algorithm 10.11): either a proper nontrivial
divisor `d` of `N` (with `1 < d < N`, `d ∣ N`), or `failure`. -/
inductive ECMResult (N : ℕ) where
  | factor (d : ℕ) (hd_gt : 1 < d) (hd_lt : d < N) (hd_dvd : d ∣ N) : ECMResult N
  | failure : ECMResult N

end
