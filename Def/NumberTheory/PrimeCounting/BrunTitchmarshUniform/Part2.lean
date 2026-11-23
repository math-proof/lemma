/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/BrunTitchmarshUniform.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Def.NumberTheory.PrimeCounting.ResidueClass
public import Theorem.Nat.PrimeCounting.ResidueClass
public import Theorem.Nat.SelbergSieve
public import Mathlib.Data.Int.CardIntervalMod
public import Mathlib.NumberTheory.EulerProduct.Basic
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Def.NumberTheory.SelbergSieve
public import Mathlib.NumberTheory.SmoothNumbers
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Theorem.NumberTheory.PrimeCounting.BrunTitchmarshUniform

@[expose] public section

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
