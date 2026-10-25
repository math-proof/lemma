/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/BPP.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TheoryOfComputation.code.Complexity.Part2
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.Complexity
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.Order.Ring.Unbundled.Rat
import Def.v1.Atlas.TheoryOfComputation.code.BPP


namespace TuringMachine

open TuringMachine

variable {Q : Type} {Γ : Type} [DecidableEq Q] [DecidableEq Γ]

/-- Decidability of acceptance along a fixed coin-flip branch, used to count
accepting branches via `Finset.filter`. -/
instance (M : PTM Q Γ) (w : List Γ) (n : ℕ) (coins : Fin n → Bool) :
    Decidable (M.acceptsWithCoins w n coins) :=
  inferInstanceAs (Decidable ((M.runWithCoins w n coins).state = M.qAccept))

/-- Decidability of rejection along a fixed coin-flip branch. -/
instance (M : PTM Q Γ) (w : List Γ) (n : ℕ) (coins : Fin n → Bool) :
    Decidable (M.rejectsWithCoins w n coins) :=
  inferInstanceAs (Decidable ((M.runWithCoins w n coins).state = M.qReject))

end TuringMachine
