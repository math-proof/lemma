module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Def.NumberTheory.PrimeCounting.ResidueClass
public import Theorem.Nat.PrimeCounting.ResidueClass
public import Theorem.Nat.PrimeCounting.WeightedLargeSieve
public import Theorem.Nat.PrimeCounting.ArithmeticLargeSieve
public import Theorem.Nat.PrimeCounting.SquarefreeTotientWeighted
public import Def.NumberTheory.PrimeCounting.WeightedLargeSieve
public import Def.NumberTheory.PrimeCounting.ArithmeticLargeSieve.Part3
public import Def.NumberTheory.PrimeCounting.SquarefreeTotientWeighted
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.Monotone
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Int.CardIntervalMod
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/BrunTitchmarsh.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
/-!
# Brun–Titchmarsh inequality

This file records the standard upper bound for primes in one residue class.
-/
namespace MathlibExt.NumberTheory.PrimeCounting.BrunTitchmarshWanted

noncomputable def btSieveFunction (α β v : ℝ) : ℝ :=
  (α + β / v) * Real.log v

noncomputable def btInvNat : ℕ →* ℝ where
  toFun n := (n : ℝ)⁻¹
  map_one' := by simp
  map_mul' m n := by simp only [Nat.cast_mul, mul_inv]

noncomputable def btInv : ArithmeticFunction ℝ :=
  ⟨btInvNat, by simp [btInvNat]⟩

def btPrimes (z q : ℕ) : Finset ℕ :=
  (Finset.range (z + 1)).filter fun p ↦ p.Prime ∧ ¬p ∣ q

def btPrimeProduct (z q : ℕ) : ℕ :=
  ∏ p ∈ btPrimes z q, p

end MathlibExt.NumberTheory.PrimeCounting.BrunTitchmarshWanted
