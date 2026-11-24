module
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Basic
public import Def.Combinatorics.Schnirelmann
public import Theorem.Finset.Schnirelmann
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.Analysis.PSeries
public import Mathlib.Data.Int.CardIntervalMod
public import Mathlib.Data.Int.NatAbs
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Tactic
public import Def.NumberTheory.HilbertWaring.Part15


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/HilbertWaring.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/
/-!
# Hilbert–Waring theorem

This file proves the Hilbert–Waring theorem by Linnik's elementary method. It develops
divisor-counting estimates and an inductive mean-value bound for polynomial Weyl sums, then
combines them with Schnirelmann's sumset inequality to obtain a finite additive basis of power sums.
-/
namespace MathlibExt.NumberTheory.HilbertWaringWanted

open Finset

open scoped Pointwise

/--
For every `k ≥ 1` there exists `g : ℕ` such that every `n : ℕ` is a sum of `g` `k`th powers: `∃ x
: Fin g → ℕ, n = ∑ i, (x i) ^ k`. Source: D. Hilbert, Beweis für die Darstellbarkeit der ganzen
Zahlen durch eine feste Anzahl n-ter Potenzen (Waringsches Problem), Math. Ann. 67 (1909) 281–305;
textbook in Vaughan, The Hardy-Littlewood Method; general includes minimal g(k).

Proves `Wanted` entry `hilbert_waring`.

Proof: We follow Linnik's elementary route as presented in Tim Jameson's notes: a mean-value
estimate gives positive Schnirelmann density for a bounded power sumset, which is then an additive
basis of finite order by Schnirelmann's inequality.
-/
theorem hilbert_waring :
    ∀ k : ℕ, 0 < k → ∃ g : ℕ, ∀ n : ℕ, ∃ x : Fin g → ℕ,
      n = Finset.univ.sum fun i => (x i) ^ k := by
  intro k hk
  by_cases hk1 : k = 1
  · subst k
    refine ⟨1, fun n ↦ ⟨fun _ ↦ n, ?_⟩⟩
    simp
  · have hk2 : 2 ≤ k := by omega
    obtain ⟨C, hC, hbound⟩ := hw_exists_powerFiber_bound k hk2
    let s := 8 ^ (k - 1)
    let A := hwPowerSumset k s
    let _ : DecidablePred (· ∈ A) := fun n ↦ Classical.propDecidable (n ∈ A)
    have hs : 0 < s := by positivity
    have hA0 : 0 ∈ A := hwPowerSumset_zero_mem hk
    have hσ : 0 < schnirelmannDensity A := by
      simpa only [A, s] using
        hw_power_sumset_density_pos_of_fiber_bound k C hk2 hC hbound
    obtain ⟨h, hbasis⟩ := exists_additive_basis_of_pos_schnirelmannDensity hA0 hσ
    refine ⟨h * s, fun n ↦ ?_⟩
    obtain ⟨z, hzA, hzn⟩ := hbasis n
    have hrep : ∀ i, ∃ x : Fin s → ℕ, z i = ∑ j, x j ^ k := by
      intro i
      exact hzA i
    choose x hx using hrep
    obtain ⟨y, hy⟩ := hw_sum_flatten h s k x
    refine ⟨y, ?_⟩
    calc
      n = ∑ i, z i := hzn
      _ = ∑ i, ∑ j, x i j ^ k := by
        apply Finset.sum_congr rfl
        intro i _
        exact hx i
      _ = ∑ i, y i ^ k := hy.symm

end MathlibExt.NumberTheory.HilbertWaringWanted
