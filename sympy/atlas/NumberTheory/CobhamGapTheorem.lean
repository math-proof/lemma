/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/CobhamGapTheorem.lean -/

import sympy.atlas.NumberTheory.BaseRecognizable
import Lemma.Nat.BaseRecognizable
import Mathlib.Basic.ENNReal.Operations
import Mathlib.Order.LiminfLimsup
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Basic.ENNReal.Inv
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic.Bound
import Mathlib.Tactic.Ring

/-!
# Cobham's gap theorem

This file proves Cobham's gap theorem for the recognizable-set API
`MetaMathlibExt.IsBaseRecognizable` from `MathlibExt.NumberTheory.BaseRecognizable`.

Source: T. Kärki, A. Lacroix, and M. Rigo, *On the Recognizability of
Self-Generating Sets*, Journal of Integer Sequences 13 (2010),
<https://cs.uwaterloo.ca/journals/JIS/VOL13/Rigo/rigo6.tex>.
Complete TeX SHA-256:
`df5d17d81e344c0c20304f1d98d35c7e263a67dcb043e6b62307fb793e4810d5`.
Recognizability definition lines 110–120, no-final-newline span SHA-256:
`bf0c0a1817a739be85df010f9aa344e0c32cf717290202a23c3ada75eac9a03d`.
Gap notation and theorem lines 979–995, no-final-newline span SHA-256:
`f968765f1533988a25b2111265bcd9cf0354f4d738e3f9440a1d18e086baee3b`.

The source writes an infinite ordered set as `X = {x₀ < x₁ < ...}` and says
either the limsup of `x_(i+1)/x_i` is greater than one or consecutive gaps
are uniformly bounded. `StrictMono x` makes `Set.range x` infinite and gives
its consecutive increasing enumeration. `ENNReal` is intentional so an
unbounded ratio limsup is `⊤`. If `x 0 = 0`, the index-zero ratio may be `⊤`;
it is a single finite-prefix term and does not affect the `atTop` limsup.
Natural subtraction is exact under strict monotonicity.
-/

section
namespace MetaMathlibExt

private def paddedDigits {k : ℕ} (hk : 2 ≤ k) (r n : ℕ) : List (Fin k) :=
  List.replicate (r - (baseDigits hk n).length) ⟨0, by omega⟩ ++ baseDigits hk n
end MetaMathlibExt
