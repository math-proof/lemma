import sympy.stats.stochastic_process_types
import sympy.stats.stochastic_process
import Lemma.Matrix.Any_And_DoeblinMinorizationPow.is.Nonempty.Aperiodic
import Lemma.Matrix.Any_And_ContractingWith.of.DoeblinMinorization
import Lemma.Matrix.Any_And_Stationary.of.RowStochastic
import Lemma.Matrix.Stationary_Pow.of.Stationary
import Lemma.Matrix.GetIterateSmatAsOperator.eq.ToLp1VecMulOfLp_Pow.of.Simplex
import Lemma.Matrix.LeNormOfL1SubVecMulS.of.RowStochastic
import Lemma.Matrix.Norm.eq.Sum_AbsOfLp
import Lemma.Matrix.L1Norm.eq.One.of.StochasticVec
open Matrix


@[main]
private lemma main
  {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
  {P : Matrix S S ℝ} [RowStochastic P]
-- given
  (h₀ : Aperiodic P)
  (h₁ : StochasticIrreducible P) :
-- imply
  GeometricMixing P := by
-- proof
  obtain ⟨μ, hμ, hμP⟩ := Any_And_Stationary.of.RowStochastic (P := P)
  obtain ⟨N, hN, hD⟩ := Any_And_DoeblinMinorizationPow.of.Nonempty.Aperiodic (P := P) inferInstance h₀
  obtain ⟨K, hK, hf⟩ := Any_And_ContractingWith.of.DoeblinMinorization hD
  let μ' : Simplex S := ⟨ofL1 μ, by simpa [ofL1] using hμ⟩
  have hfix : Function.IsFixedPt (smat_as_operator (P ^ N)) μ' := by
    apply Subtype.ext
    simp [μ', smat_as_operator, ofL1]
    exact (Stationary_Pow.of.Stationary hμP (n := N)).stationary
  have hK1 : (K : ℝ) < 1 := hf.1
  have hKpos : (0 : ℝ) < K := hK
  have hdist : ∀ (x : S → ℝ), StochasticVec x → ∀ q : ℕ, ∑ s, |(x ᵥ* (P ^ N) ^ q - μ) s| ≤ 2 * (K : ℝ) ^ q := by
    intro x hx q
    let x' : Simplex S := ⟨ofL1 x, by simpa [ofL1] using hx⟩
    have h := (hf.2.iterate q).dist_le_mul x' μ'
    rw [hfix.iterate q, Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm,
      GetIterateSmatAsOperator.eq.ToLp1VecMulOfLp_Pow.of.Simplex] at h
    have h2 : ‖(x' : l1Space S) - (μ' : l1Space S)‖ ≤ 2 := by
      calc _ ≤ ‖(x' : l1Space S)‖ + ‖(μ' : l1Space S)‖ := norm_sub_le _ _
        _ = 2 := by
          simp only [x', μ', L1Norm.eq.One.of.StochasticVec hx, L1Norm.eq.One.of.StochasticVec hμ]
          norm_num
    have h3 := h.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
    rw [Norm.eq.Sum_AbsOfLp] at h3
    simp [x', μ', ofL1] at h3
    rw [← pow_mul] at h3 ⊢
    simpa [mul_comm] using h3
  refine ⟨⟨2 / K, (K : ℝ) ^ (1 / (N : ℝ)), μ, by positivity, by positivity,
    Real.rpow_lt_one hKpos.le hK1 (by positivity), hμ, hμP, ?_⟩⟩
  intro x hx n
  have hNpos : 0 < N := by omega
  have hr : Stationary μ (P ^ (n % N)) := Stationary_Pow.of.Stationary hμP
  have hsplit : x ᵥ* P ^ n - μ ᵥ* P ^ (n % N) = x ᵥ* (P ^ N) ^ (n / N) ᵥ* P ^ (n % N) - μ ᵥ* P ^ (n % N) := by
    rw [vecMul_vecMul, ← pow_mul, ← pow_add, Nat.div_add_mod]
  have hle := LeNormOfL1SubVecMulS.of.RowStochastic (Q := P ^ (n % N)) inferInstance (x ᵥ* (P ^ N) ^ (n / N)) μ
  rw [← hsplit, hr.stationary, Norm.eq.Sum_AbsOfLp, Norm.eq.Sum_AbsOfLp] at hle
  have hq := hdist x hx (n / N)
  simp at hle hq ⊢
  refine (hle.trans hq).trans ?_
  have hq' : (n : ℝ) / N - 1 ≤ ((n / N : ℕ) : ℝ) := by
    have h1 := Nat.lt_mul_div_succ n hNpos
    have h2 : (n : ℝ) < N * ((n / N : ℕ) + 1) := by exact_mod_cast h1
    rw [div_sub_one (by positivity), div_le_iff₀ (by positivity)]
    linarith
  have hpow : (K : ℝ) ^ (n / N) ≤ (K : ℝ) ^ ((n : ℝ) / N - 1) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge hKpos hK1.le hq'
  have heq : 2 / (K : ℝ) * ((K : ℝ) ^ (1 / (N : ℝ))) ^ n = 2 * (K : ℝ) ^ ((n : ℝ) / N - 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hKpos.le, Real.rpow_sub hKpos, Real.rpow_one]
    field_simp
  rw [one_div] at heq
  rw [heq]
  linarith


-- created on 2026-09-26