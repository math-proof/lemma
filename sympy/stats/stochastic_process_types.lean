import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Data.Matrix.Basic
import sympy.sets.handlers.add
import sympy.core.intfunc

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

universe u

-- L1 space over S (typically, Fin n)
abbrev l1Space (S : Type u) := WithLp 1 (S → ℝ)

-- reinterpret a score vector as a point of l1Space
noncomputable abbrev ofL1 {S : Type u} (x : S → ℝ) : l1Space S :=
  (WithLp.equiv 1 (S → ℝ)).symm x

-- categorical distribution on finite S ↔ StochasticVec x (e.g. a softmax output)
class StochasticVec {S : Type u} [Fintype S] (x : S → ℝ) : Prop where
  nonneg : ∀ s, 0 ≤ x s
  rowsum : ∑ s, x s = 1

-- Probability simplex on S: {x | x ≥ 0, ∑ x = 1} inside l1Space S.
-- Geometrically: a 0-simplex is a point, 1-simplex a segment, 2-simplex a triangle, 3-simplex a tetrahedron, … (here dimension is |S| - 1).
abbrev Simplex (S : Type u) [Fintype S] :=
  {x : l1Space S | StochasticVec (WithLp.ofLp x)}

-- asserts that P is a Markov transition matrix, wherein P i j is the probability of going from current tag/state i to next tag/state j in one step.
class RowStochastic {S : Type u} [Fintype S] (P : Matrix S S ℝ) : Prop where
  stochastic : ∀ s, StochasticVec (P s)

-- assumes every state can reach every other with positive probability in finite steps
class StochasticIrreducible {S : Type u} [Fintype S] [DecidableEq S]
    (P : Matrix S S ℝ) [RowStochastic P] : Prop where
  irreducible : ∀ i j, ∃ n : ℕ, 0 < (P ^ n) i j

-- step counts at which a tag/state i can recur with positive probability in sequence-modeling tasks
noncomputable def return_times {S : Type u} [Fintype S] [DecidableEq S]
    (P : Matrix S S ℝ) [RowStochastic P] (i : S) : Set ℕ :=
  {n : ℕ | 1 ≤ n ∧ 0 < (P ^ n) i i}

-- no fixed period for revisiting a tag/state (useful so long tag sequences are not stuck on even/odd steps, etc.)
class Aperiodic {S : Type u} [Fintype S] [DecidableEq S]
    (P : Matrix S S ℝ) [RowStochastic P] : Prop where
  aperiodic : ∀ i, FiniteGCDOne (return_times P i)

instance {S : Type u} [Fintype S] [DecidableEq S]
    (P : Matrix S S ℝ) [RowStochastic P] [Aperiodic P] (i : S) :
    FiniteGCDOne (return_times P i) :=
  Aperiodic.aperiodic (P := P) i

-- shared background next-tag floor: every row of P keeps at least mass ε on the same categorical ν
class DoeblinMinorization {S : Type u} [Fintype S]
    (P : Matrix S S ℝ) [RowStochastic P] : Prop where
  minorize : ∃ (ε : ℝ) (ν : S → ℝ),
    0 < ε ∧ ε < 1 ∧ StochasticVec ν ∧ ∀ i j, P i j ≥ ε * ν j

-- stationary / equilibrium tag distribution: long-run tag frequencies μ unchanged by one more transition
class Stationary {S : Type u} [Fintype S] (μ : S → ℝ) (P : Matrix S S ℝ) : Prop where
  stationary : μ ᵥ* P = μ

-- no matter how you start to utter, finally you will utter the same kind of stories you like to utter
-- tag mix → stationary μ
-- ρ = forget-rate, geometric convergence to μ
class GeometricMixing {S : Type u} [Fintype S] [DecidableEq S]
    (P : Matrix S S ℝ) [RowStochastic P] : Prop where
  mixing : ∃ (C ρ : ℝ) (μ : S → ℝ),
    0 < C ∧ 0 < ρ ∧ ρ < 1 ∧ StochasticVec μ ∧ Stationary μ P ∧
    ∀ (x : S → ℝ) [StochasticVec x] (n : ℕ),
      (∑ s, |(x ᵥ* (P ^ n) - μ) s|) ≤ C * ρ ^ n

-- broadcast a vector to a matrix row-wisely
def broadcast {S : Type u} [Fintype S] (ν : S → ℝ) : Matrix S S ℝ :=
  Matrix.of fun _ s' => ν s'

-- the ordinary sample mean of the path, x₀, x₀P, …, x₀Pⁿ
noncomputable def cesaro_average {S : Type u} [Fintype S] [DecidableEq S]
    (x₀ : S → ℝ) [StochasticVec x₀] (P : Matrix S S ℝ) [RowStochastic P] (n : ℕ) :
    S → ℝ :=
  (n + 1 : ℝ)⁻¹ • ∑ k ∈ Finset.range (n + 1), x₀ ᵥ* (P ^ k)

noncomputable abbrev uniform_distribution {S : Type u} [Fintype S] : S → ℝ :=
  fun _ => 1 / Fintype.card S

-- result of composing two tag-transition matrices is still a valid transition matrix
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
    have := ih
    simpa [pow_succ] using smat_mul_smat_is_smat (P ^ n) P

-- probability of an m+n-step i→j path is at least the product of an m-step i→k
-- path and an n-step k→j path (all other decompositions are nonneg)
lemma get_pow_add_ge_mul_get_s_pow {S : Type u} [Fintype S] [DecidableEq S]
    {P : Matrix S S ℝ} [RowStochastic P] (m n : ℕ) (i j k : S) :
    (P ^ (m + n)) i j ≥ (P ^ m) i k * (P ^ n) k j := by
  have := smat_pow_is_smat (P := P) m
  have := smat_pow_is_smat (P := P) n
  rw [pow_add]
  simp [Matrix.mul_apply]
  rw [← Finset.sum_erase_add (a := k)]
  · apply le_add_of_nonneg_left
    apply Finset.sum_nonneg
    intro l hl
    apply mul_nonneg <;>
      apply (RowStochastic.stochastic _).nonneg
  · simp

-- return times are closed under addition: positive i→i paths of lengths a and b
-- concatenate into a positive i→i path of length a + b
instance return_times_closedUnderAdd {S : Type u} [Fintype S] [DecidableEq S]
    (P : Matrix S S ℝ) [RowStochastic P] (i : S) :
    ClosedUnderAdd (return_times P i) where
  closed_under_add a b ha hb := by
    simp only [return_times, Set.mem_ofPred_eq] at ha hb ⊢
    obtain ⟨ha1, ha2⟩ := ha
    obtain ⟨hb1, hb2⟩ := hb
    refine ⟨by linarith, ?_⟩
    calc
      _ < (P ^ a) i i * (P ^ b) i i := mul_pos ha2 hb2
      _ ≤ (P ^ (a + b)) i i :=
          (get_pow_add_ge_mul_get_s_pow (P := P) a b i i i).le

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

-- uniform_distribution is always stochastic
instance uniform_distribution_stochastic {S : Type u} [Fintype S] [Nonempty S] :
    StochasticVec (S := S) uniform_distribution where
  nonneg s := by simp [uniform_distribution]
  rowsum := by
    simp [uniform_distribution, Finset.sum_const, Finset.card_univ]
