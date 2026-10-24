/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Tableau.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.TheoryOfComputation.code.Complexity
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.Complexity
namespace TuringMachine

open TuringMachine

/--
A **cell symbol** that may appear in a single cell of a Cook-Levin tableau:
either a tape symbol `γ ∈ Γ` (representing tape contents) or a state `q ∈ Q`
(marking the head position together with the current state).
-/
abbrev CellSymbol (Q : Type) (Γ : Type) := Q ⊕ Γ

variable {Q : Type} {Γ : Type} [DecidableEq Q]

/--
Encode a TM configuration `c` as one **row** of a tableau of given `width`:
position `j` holds the state `c.state` (as `Sum.inl`) if the head is over cell
`j`, and otherwise the tape symbol `c.tape j` (as `Sum.inr`).
-/
def encodeConfigRow (c : Config Q Γ) (width : ℕ) : Fin width → CellSymbol Q Γ :=
  fun j =>
    if (j : ℤ) = c.headPos then Sum.inl c.state
    else Sum.inr (c.tape j)

/--
`IsLegalWindow M a b c d e f` says that the 2 × 3 window
```
a b c
d e f
```
is consistent with one step of the NTM `M`: the top row `(a, b, c)` is the
parent and the bottom row `(d, e, f)` is the child. There are two cases:

1. **No head in the top window.** If none of `a, b, c` is a state symbol, then
   the cell directly below `b` must equal `b` (the tape doesn't change away from
   the head).
2. **Head at the centre.** If `b = ⟨q⟩` for some state `q` and the tape symbol
   above `b` is `γ`, then there must be some transition
   `(q', γ', dir) ∈ M.δ q γ` consistent with the bottom row, or the window may
   alternatively show no change (`e = γ`).

This is the local-consistency predicate used in the Cook-Levin tableau argument.
-/
def IsLegalWindow (M : NTM Q Γ)
    (a b c d e f : CellSymbol Q Γ) : Prop :=

  (((∀ q : Q, a ≠ Sum.inl q) ∧ (∀ q : Q, b ≠ Sum.inl q) ∧ (∀ q : Q, c ≠ Sum.inl q))
    → e = b) ∧


  (∀ (q : Q) (γ : Γ), b = Sum.inl q →

    (∃ (q' : Q) (γ' : Γ) (dir : Direction),
      (q', γ', dir) ∈ M.δ q γ ∧
      (e = Sum.inr γ' ∨ e = Sum.inl q') ∧
      (d = a ∨ d = Sum.inl q') ∧
      (f = c ∨ f = Sum.inl q'))
    ∨ e = Sum.inr γ)

/-- Alternative name for `IsLegalWindow`: a legal 6-tuple `(a, b, c, d, e, f)` describing a 2×3 window. -/
abbrev IsLegalSextuple := @IsLegalWindow

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
