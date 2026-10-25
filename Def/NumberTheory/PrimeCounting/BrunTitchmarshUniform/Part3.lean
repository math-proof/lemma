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
import Theorem.NumberTheory.PrimeCounting.BrunTitchmarshUniform.Part2
/-!
# Uniform Brun–Titchmarsh inequality

This file proves a uniform upper bound for primes in one residue class.
-/


namespace MathlibExt.NumberTheory.PrimeCounting.BrunTitchmarshUniformWanted

open MathlibExt.SelbergSieve

noncomputable def brunTitchmarshSieve (X k ell R : ℕ) : BoundingSieve where
  support := (Finset.range (X + 1)).filter fun n ↦ n ≡ ell [MOD k]
  prodPrimes := brunTitchmarshPrimeProduct R k
  prodPrimes_squarefree := brunTitchmarshPrimeProduct_squarefree R k
  weights := fun _ ↦ 1
  weights_nonneg := fun _ ↦ zero_le_one
  totalMass := (X + 1 : ℕ) / (k : ℝ)
  nu := brunTitchmarshNu
  nu_mult := brunTitchmarshNu_mult
  nu_pos_of_prime := by
    intro p hp _
    rw [brunTitchmarshNu_apply, inv_pos]
    exact_mod_cast hp.pos
  nu_lt_one_of_prime := by
    intro p hp _
    rw [brunTitchmarshNu_apply]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)

def brunTitchmarshRadAway (k n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors.filter (fun p ↦ ¬p ∣ k), p

noncomputable def brunTitchmarshLevel (y : ℝ) : ℕ :=
  ⌊Real.rpow y (1 / 24 : ℝ)⌋₊

end MathlibExt.NumberTheory.PrimeCounting.BrunTitchmarshUniformWanted
