/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/BinomialHarmonicConvolution.lean -/

import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.Data.Rat.Star
import Mathlib.GroupTheory.Finiteness
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.Positivity.Basic


namespace MetaMathlibExt

def Lsum (a b : ℕ) : ℚ :=
  ∑ ν ∈ Finset.Icc 1 (a + 1),
    ((((Nat.choose (a + b + 1 - ν) a : ℕ)) : ℚ) -
     (((Nat.choose (a + b + 1 - ν) b : ℕ)) : ℚ)) * harmonic ν

def Rval (a b : ℕ) : ℚ :=
  ((Nat.choose (a + b + 2) (b + 1) : ℕ) : ℚ) * (harmonic (b + 1) - harmonic (a + 1))

end MetaMathlibExt
