import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Data.Matrix.Basic
import Lemma.Set.InMul.of.In.Gt_0
import Lemma.Set.Any_All_In.of.ClosedUnderAdd.FiniteGCDOne

/-!
# Stochastic process types (DiscreteMarkovChain)

Finite discrete-time homogeneous Markov-chain primitives, aligned with
[sympy.stats.stochastic_process_types.DiscreteMarkovChain](https://github.com/sympy/sympy/blob/master/sympy/stats/stochastic_process_types.py).

In Lean these are typeclasses on a transition matrix `P : Matrix S S ℝ`
(`RowStochastic`, `StochasticIrreducible`, `Aperiodic`) plus the probability
simplex `StochasticVec` / `Simplex`, rather than a single Python class.
-/
open Finset Matrix WithLp Set
open scoped Matrix BigOperators

namespace StochasticMatrix

universe u

abbrev l1Space (S : Type u) := WithLp 1 (S → ℝ)

noncomputable abbrev ofL1 {S : Type u} (x : S → ℝ) : l1Space S :=
  (WithLp.equiv 1 (S → ℝ)).symm x

class StochasticVec {S : Type u} [Fintype S] (x : S → ℝ) : Prop where
  nonneg : ∀ s, 0 ≤ x s
  rowsum : ∑ s, x s = 1

abbrev Simplex (S : Type u) [Fintype S] :=
  {x : l1Space S | StochasticVec (WithLp.ofLp x)}

class RowStochastic {S : Type u} [Fintype S] (P : Matrix S S ℝ) : Prop where
  stochastic : ∀ s, StochasticVec (P s)

class StochasticIrreducible {S : Type u} [Fintype S] [DecidableEq S]
    (P : Matrix S S ℝ) [RowStochastic P] : Prop where
  irreducible : ∀ i j, ∃ n : ℕ, 0 < (P ^ n) i j

noncomputable def return_times {S : Type u} [Fintype S] [DecidableEq S]
    (P : Matrix S S ℝ) [RowStochastic P] (i : S) : Set ℕ :=
  {n : ℕ | 1 ≤ n ∧ 0 < (P ^ n) i i}

class Aperiodic {S : Type u} [Fintype S] [DecidableEq S]
    (P : Matrix S S ℝ) [RowStochastic P] : Prop where
  aperiodic : ∀ i, FiniteGCDOne (return_times P i)

instance {S : Type u} [Fintype S] [DecidableEq S]
    (P : Matrix S S ℝ) [RowStochastic P] [Aperiodic P] (i : S) :
    FiniteGCDOne (return_times P i) :=
  Aperiodic.aperiodic (P := P) i

class DoeblinMinorization {S : Type u} [Fintype S]
    (P : Matrix S S ℝ) [RowStochastic P] : Prop where
  minorize : ∃ (ε : ℝ) (ν : S → ℝ),
    0 < ε ∧ ε < 1 ∧ StochasticVec ν ∧ ∀ i j, P i j ≥ ε * ν j

class Stationary {S : Type u} [Fintype S] (μ : S → ℝ) (P : Matrix S S ℝ) : Prop where
  stationary : μ ᵥ* P = μ

class GeometricMixing {S : Type u} [Fintype S] [DecidableEq S]
    (P : Matrix S S ℝ) [RowStochastic P] : Prop where
  mixing : ∃ (C ρ : ℝ) (μ : S → ℝ),
    0 < C ∧ 0 < ρ ∧ ρ < 1 ∧ StochasticVec μ ∧ Stationary μ P ∧
    ∀ (x : S → ℝ) [StochasticVec x] (n : ℕ),
      (∑ s, |(x ᵥ* (P ^ n) - μ) s|) ≤ C * ρ ^ n

def broadcast {S : Type u} [Fintype S] (ν : S → ℝ) : Matrix S S ℝ :=
  Matrix.of fun _ s' => ν s'

noncomputable def cesaro_average {S : Type u} [Fintype S] [DecidableEq S]
    (x₀ : S → ℝ) [StochasticVec x₀] (P : Matrix S S ℝ) [RowStochastic P] (n : ℕ) :
    S → ℝ :=
  (n + 1 : ℝ)⁻¹ • ∑ k ∈ Finset.range (n + 1), x₀ ᵥ* (P ^ k)

noncomputable abbrev uniform_distribution {S : Type u} [Fintype S] : S → ℝ :=
  fun _ => 1 / Fintype.card S

instance smat_mul_smat_is_smat {S : Type u} [Fintype S]
    (P Q : Matrix S S ℝ) [hP : RowStochastic P] [hQ : RowStochastic Q] :
    RowStochastic (P * Q) where
  stochastic i := by
    refine ⟨?nonneg, ?rowsum⟩
    · intro j
      have : 0 ≤ ∑ k, P i k * Q k j :=
        sum_nonneg fun k _ =>
          mul_nonneg (hP.stochastic i |>.nonneg k) (hQ.stochastic k |>.nonneg j)
      simpa [Matrix.mul_apply] using this
    · calc
          ∑ j, (P * Q) i j
        _ = ∑ j, ∑ k, P i k * Q k j := by simp [Matrix.mul_apply]
        _ = ∑ k, ∑ j, P i k * Q k j := by rw [sum_comm]
        _ = ∑ k, P i k * ∑ j, Q k j := by
            apply sum_congr rfl; intro k _; simp [mul_sum]
        _ = ∑ k, P i k := by
            apply sum_congr rfl; intro k _; simp [(hQ.stochastic k).rowsum]
        _ = 1 := (hP.stochastic i).rowsum

instance smat_pow_is_smat {S : Type u} [Fintype S] [DecidableEq S]
    (P : Matrix S S ℝ) [RowStochastic P] (n : ℕ) : RowStochastic (P ^ n) := by
  induction n with
  | zero =>
    refine ⟨fun i => ⟨?_, ?_⟩⟩
    · intro j
      by_cases h : i = j
      · subst h; simp
      · simp [Matrix.one_apply_ne h]
    · simp [Matrix.one_apply]
  | succ n ih =>
    haveI := ih
    simpa [pow_succ] using smat_mul_smat_is_smat (P ^ n) P

instance svec_mul_smat_is_svec {S : Type u} [Fintype S]
    (μ : S → ℝ) [hμ : StochasticVec μ] (P : Matrix S S ℝ) [hP : RowStochastic P] :
    StochasticVec (μ ᵥ* P) where
  nonneg j := by
    have : 0 ≤ ∑ i, μ i * P i j :=
      sum_nonneg fun i _ => mul_nonneg (hμ.nonneg i) ((hP.stochastic i).nonneg j)
    simpa [Matrix.vecMul, dotProduct] using this
  rowsum := by
    change ∑ j, ∑ i, μ i * P i j = 1
    rw [sum_comm]
    calc
        ∑ i, ∑ j, μ i * P i j
      _ = ∑ i, μ i * ∑ j, P i j := by
          apply sum_congr rfl; intro i _; rw [← mul_sum]
      _ = ∑ i, μ i := by
          apply sum_congr rfl; intro i _; rw [(hP.stochastic i).rowsum, mul_one]
      _ = 1 := hμ.rowsum

instance uniform_distribution_stochastic {S : Type u} [Fintype S] [Nonempty S] :
    StochasticVec (S := S) uniform_distribution where
  nonneg s := by simp [uniform_distribution]
  rowsum := by
    simp [uniform_distribution, Finset.sum_const, Finset.card_univ]

end StochasticMatrix
