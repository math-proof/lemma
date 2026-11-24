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
public import Def.NumberTheory.PrimeCounting.BrunTitchmarshUniform.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/BrunTitchmarshUniform.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
/-!
# Uniform Brun–Titchmarsh inequality

This file proves a uniform upper bound for primes in one residue class.
-/
namespace MathlibExt.NumberTheory.PrimeCounting.BrunTitchmarshUniformWanted

open MathlibExt.SelbergSieve

theorem brunTitchmarshPrimeProduct_squarefree (R k : ℕ) :
    Squarefree (brunTitchmarshPrimeProduct R k) := by
  unfold brunTitchmarshPrimeProduct brunTitchmarshPrimes
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hp hq
    exact (Nat.coprime_iff_isRelPrime.mp <| (Nat.coprime_primes hp.2.1 hq.2.1).mpr hpq)
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp
    exact hp.2.1.prime.squarefree

end MathlibExt.NumberTheory.PrimeCounting.BrunTitchmarshUniformWanted
