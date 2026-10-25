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
import Def.NumberTheory.PrimeCounting.BrunTitchmarshUniform
/-!
# Uniform Brun–Titchmarsh inequality

This file proves a uniform upper bound for primes in one residue class.
-/


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
