/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/HigherOrderHarmonic.lean -/

module

public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Field.Rat

@[expose] public section

/-- Higher-order harmonic numbers: `H_n^(r) = ∑_{k=1}^n 1 / k ^ r` as rationals. -/
def higherHarmonic (n r : Nat) : Rat :=
  ∑ k ∈ Finset.Icc 1 n, (1 : Rat) / ((k : Rat) ^ r)

