/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Tableau.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TheoryOfComputation.code.Complexity.Part2
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.Complexity
import Abbrev.v1.Atlas.TheoryOfComputation.code.Tableau


namespace TuringMachine

open TuringMachine

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

end TuringMachine
