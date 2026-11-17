/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/BinomialHarmonicConvolution.lean -/

module

public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star
public import Mathlib.Data.Rat.Star
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Positivity.Basic

@[expose] public section

namespace MetaMathlibExt

def Lsum (a b : ℕ) : ℚ :=
  ∑ ν ∈ Finset.Icc 1 (a + 1),
    ((((Nat.choose (a + b + 1 - ν) a : ℕ)) : ℚ) -
     (((Nat.choose (a + b + 1 - ν) b : ℕ)) : ℚ)) * harmonic ν

def Rval (a b : ℕ) : ℚ :=
  ((Nat.choose (a + b + 2) (b + 1) : ℕ) : ℚ) * (harmonic (b + 1) - harmonic (a + 1))

end MetaMathlibExt
