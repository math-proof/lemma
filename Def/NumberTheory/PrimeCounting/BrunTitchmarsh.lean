/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/BrunTitchmarsh.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Def.NumberTheory.PrimeCounting.ResidueClass
import Lemma.Nat.PrimeCounting.ResidueClass
import Lemma.Nat.PrimeCounting.WeightedLargeSieve
import Lemma.Nat.PrimeCounting.ArithmeticLargeSieve
import Lemma.Nat.PrimeCounting.SquarefreeTotientWeighted
import Def.NumberTheory.PrimeCounting.WeightedLargeSieve
import Def.NumberTheory.PrimeCounting.ArithmeticLargeSieve.Part3
import Def.NumberTheory.PrimeCounting.SquarefreeTotientWeighted
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
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
