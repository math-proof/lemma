/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/BrunTitchmarshUniform.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import sympy.atlas.NumberTheory.PrimeCounting.ResidueClass
import Lemma.Nat.PrimeCounting.ResidueClass
import Lemma.Nat.SelbergSieve
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import sympy.atlas.NumberTheory.SelbergSieve
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Uniform Brun–Titchmarsh inequality

This file proves a uniform upper bound for primes in one residue class.
-/

namespace MathlibExt.NumberTheory.PrimeCounting.BrunTitchmarshUniformWanted

open MathlibExt.SelbergSieve

private noncomputable def brunTitchmarshInvNat : ℕ →* ℝ where
  toFun n := (n : ℝ)⁻¹
  map_one' := by simp
  map_mul' m n := by simp only [Nat.cast_mul, mul_inv]

private noncomputable def brunTitchmarshNu : ArithmeticFunction ℝ :=
  ⟨brunTitchmarshInvNat, by simp [brunTitchmarshInvNat]⟩

@[simp] private theorem brunTitchmarshNu_apply (n : ℕ) :
    brunTitchmarshNu n = (n : ℝ)⁻¹ := rfl

private theorem brunTitchmarshNu_mult : brunTitchmarshNu.IsMultiplicative := by
  constructor
  · simp
  · intro m n _
    simp only [brunTitchmarshNu_apply, Nat.cast_mul, mul_inv]

private def brunTitchmarshPrimes (R k : ℕ) : Finset ℕ :=
  (Finset.range (R + 1)).filter fun p ↦ p.Prime ∧ ¬p ∣ k

private def brunTitchmarshPrimeProduct (R k : ℕ) : ℕ :=
  ∏ p ∈ brunTitchmarshPrimes R k, p

private theorem brunTitchmarshPrimeProduct_squarefree (R k : ℕ) :
    Squarefree (brunTitchmarshPrimeProduct R k) := by
  unfold brunTitchmarshPrimeProduct brunTitchmarshPrimes
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hp hq
    exact (Nat.coprime_iff_isRelPrime.mp <| (Nat.coprime_primes hp.2.1 hq.2.1).mpr hpq)
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp
    exact hp.2.1.prime.squarefree

private noncomputable def brunTitchmarshSieve (X k ell R : ℕ) : BoundingSieve where
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

private def brunTitchmarshRadAway (k n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors.filter (fun p ↦ ¬p ∣ k), p

private noncomputable def brunTitchmarshLevel (y : ℝ) : ℕ :=
  ⌊Real.rpow y (1 / 24 : ℝ)⌋₊
end MathlibExt.NumberTheory.PrimeCounting.BrunTitchmarshUniformWanted
