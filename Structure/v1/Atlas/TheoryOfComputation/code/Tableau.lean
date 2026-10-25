/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Tableau.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TheoryOfComputation.code.Complexity.Part2
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.Complexity
import Abbrev.v1.Atlas.TheoryOfComputation.code.Tableau.Part2


namespace TuringMachine

open TuringMachine

variable {Q : Type} {Γ : Type} [DecidableEq Q]

/--
An **(accepting) tableau for NTM `M` on input `w`**. Following Sipser, this is an
`nᵏ × nᵏ` table (where `n = |w|`) of `CellSymbol`s representing a computation
history on some accepting branch of `M`'s nondeterministic computation:

* `k` — the polynomial exponent giving the table's side length.
* `cell i j` — the contents of row `i`, column `j`.
* `size_pos` — the side length `nᵏ` is positive.
* `start` — row `0` is the encoding of the initial configuration of `M` on `w`.
* `accept` — the last row contains the accept state somewhere.
* `move` — every interior 2 × 3 window is a legal window
  (`IsLegalWindow M …`), enforcing that consecutive rows describe valid
  computation steps of `M`.

The existence of such a tableau is the central object in the Cook-Levin proof
that `SAT` (and `3SAT`) are NP-complete.
-/
structure Tableau (M : NTM Q Γ) (w : List Γ) where
  k : ℕ
  cell : Fin (w.length ^ k) → Fin (w.length ^ k) → CellSymbol Q Γ
  size_pos : 0 < w.length ^ k
  start : cell ⟨0, size_pos⟩ = encodeConfigRow (M.initConfig w) (w.length ^ k)
  accept : ∃ j : Fin (w.length ^ k),
    cell ⟨w.length ^ k - 1, by omega⟩ j = Sum.inl M.qAccept
  move : ∀ (i : Fin (w.length ^ k)) (hi : i.val + 1 < w.length ^ k)
         (j : Fin (w.length ^ k))
         (hj1 : 0 < j.val) (hj2 : j.val + 1 < w.length ^ k),
    IsLegalWindow M
      (cell i ⟨j.val - 1, by omega⟩)
      (cell i j)
      (cell i ⟨j.val + 1, hj2⟩)
      (cell ⟨i.val + 1, hi⟩ ⟨j.val - 1, by omega⟩)
      (cell ⟨i.val + 1, hi⟩ j)
      (cell ⟨i.val + 1, hi⟩ ⟨j.val + 1, hj2⟩)

end TuringMachine
