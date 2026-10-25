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
import Def.NumberTheory.PrimeCounting.BrunTitchmarshUniform.Part2
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
