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

@[expose] public section

/-!
# Uniform Brun–Titchmarsh inequality

This file proves a uniform upper bound for primes in one residue class.
-/


namespace MathlibExt.NumberTheory.PrimeCounting.BrunTitchmarshUniformWanted

open MathlibExt.SelbergSieve

noncomputable def brunTitchmarshInvNat : ℕ →* ℝ where
  toFun n := (n : ℝ)⁻¹
  map_one' := by simp
  map_mul' m n := by simp only [Nat.cast_mul, mul_inv]

noncomputable def brunTitchmarshNu : ArithmeticFunction ℝ :=
  ⟨brunTitchmarshInvNat, by simp [brunTitchmarshInvNat]⟩

end MathlibExt.NumberTheory.PrimeCounting.BrunTitchmarshUniformWanted
