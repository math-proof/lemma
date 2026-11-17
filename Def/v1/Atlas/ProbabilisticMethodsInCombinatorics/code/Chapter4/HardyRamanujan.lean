/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter4/HardyRamanujan.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Factorization.Basic

@[expose] public section

set_option maxHeartbeats 400000

open Filter Real Finset


noncomputable section

namespace HardyRamanujan

/-- $\omega(n)$, the number of distinct prime factors of $n$. -/
def omega (n : ℕ) : ℕ := n.primeFactors.card

end HardyRamanujan
end
