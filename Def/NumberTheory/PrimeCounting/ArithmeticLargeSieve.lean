/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/ArithmeticLargeSieve.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Def.NumberTheory.PrimeCounting.WeightedLargeSieve
public import Theorem.Nat.PrimeCounting.WeightedLargeSieve
public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Tactic

@[expose] public section

open scoped BigOperators


namespace MathlibExt.NumberTheory.PrimeCounting

def btFareyIndex (z : ℕ) :=
  {p : Fin (z + 1) × Fin (z + 1) //
    0 < p.2.1 ∧ p.1.1 < p.2.1 ∧ Nat.Coprime p.1.1 p.2.1}

end MathlibExt.NumberTheory.PrimeCounting
