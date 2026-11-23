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
public import Def.NumberTheory.PrimeCounting.BrunTitchmarshUniform

/-!
# Uniform Brun–Titchmarsh inequality

This file proves a uniform upper bound for primes in one residue class.
-/

public section


namespace MathlibExt.NumberTheory.PrimeCounting.BrunTitchmarshUniformWanted

open MathlibExt.SelbergSieve

@[simp] theorem brunTitchmarshNu_apply (n : ℕ) :
    brunTitchmarshNu n = (n : ℝ)⁻¹ := rfl

theorem brunTitchmarshNu_mult : brunTitchmarshNu.IsMultiplicative := by
  constructor
  · simp
  · intro m n _
    simp only [brunTitchmarshNu_apply, Nat.cast_mul, mul_inv]

end MathlibExt.NumberTheory.PrimeCounting.BrunTitchmarshUniformWanted
