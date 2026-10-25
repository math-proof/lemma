/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/BrunTitchmarshUniform.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Def.NumberTheory.PrimeCounting.ResidueClass
import Lemma.Nat.PrimeCounting.ResidueClass
import Lemma.Nat.SelbergSieve
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import Def.NumberTheory.SelbergSieve
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorem.NumberTheory.PrimeCounting.BrunTitchmarshUniform
/-!
# Uniform Brun–Titchmarsh inequality

This file proves a uniform upper bound for primes in one residue class.
-/


namespace MathlibExt.NumberTheory.PrimeCounting.BrunTitchmarshUniformWanted

open MathlibExt.SelbergSieve

def brunTitchmarshPrimes (R k : ℕ) : Finset ℕ :=
  (Finset.range (R + 1)).filter fun p ↦ p.Prime ∧ ¬p ∣ k

def brunTitchmarshPrimeProduct (R k : ℕ) : ℕ :=
  ∏ p ∈ brunTitchmarshPrimes R k, p

end MathlibExt.NumberTheory.PrimeCounting.BrunTitchmarshUniformWanted
