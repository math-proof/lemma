import sympy.stats.stochastic_process
import Lemma.Matrix.VecMul.Continuous
import Lemma.Matrix.NormOfL1Sub.le.Div2Add
import Lemma.Matrix.StochasticVecCesaroAverage
import Lemma.Matrix.IsCompactSimplex
import Lemma.Matrix.OfL1.eq.Sub
open WithLp Matrix Metric Topology Function PiLp
open scoped Matrix BigOperators Topology NNReal
set_option maxHeartbeats 800000


@[main]
private lemma main
  {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
  {P : Matrix S S ℝ} [RowStochastic P] :
-- imply
  ∃ μ : S → ℝ, StochasticVec μ ∧ Stationary μ P := by
-- proof
  let x0 := uniform_distribution (S := S)
  let xn : ℕ → l1Space S := fun n => ofL1 (cesaro_average x0 P n)
  have hx : ∀ n, xn n ∈ Simplex S := by
    intro n
    simpa [xn, ofL1] using Matrix.StochasticVecCesaroAverage n
  obtain ⟨mul1, hmul1, nk, hnk_mono, hnk_lim⟩ :=
    IsCompact.tendsto_subseq (Matrix.IsCompactSimplex (S := S)) hx
  refine ⟨WithLp.ofLp mul1, hmul1, ⟨?hstat⟩⟩
  case hstat =>
    have hbound :
        ∀ n, ‖ofL1 (cesaro_average x0 P (nk n) ᵥ* P -
          cesaro_average x0 P (nk n))‖ ≤ 2 / (nk n + 1 : ℝ) :=
      fun n => Matrix.NormOfL1Sub.le.Div2Add (nk n)
    have ha :
        Filter.Tendsto (fun n =>
          ‖ofL1 (cesaro_average x0 P (nk n) ᵥ* P - cesaro_average x0 P (nk n))‖)
          Filter.atTop (nhds (0 : Real)) := by
      refine squeeze_zero (fun _ => norm_nonneg _) hbound ?_
      have hnk_atTop : Filter.Tendsto nk Filter.atTop Filter.atTop := hnk_mono.tendsto_atTop
      have h1 : Filter.Tendsto (fun m : Nat => (1 : Real) / (m + 1)) Filter.atTop (nhds (0 : Real)) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have hdiv0 :
          Filter.Tendsto (fun m : Nat => (2 : Real) * ((1 : Real) / (m + 1))) Filter.atTop
            (nhds (0 : Real)) := by
        simpa using (h1.const_mul (2 : Real))
      have hdiv0' :
          Filter.Tendsto (fun m : Nat => (2 : Real) / (m + 1)) Filter.atTop (nhds (0 : Real)) := by
        convert hdiv0 using 1
        funext m
        ring
      exact hdiv0'.comp hnk_atTop
    have hxa :
        Filter.Tendsto (fun n =>
          ofL1 (cesaro_average x0 P (nk n) ᵥ* P - cesaro_average x0 P (nk n)))
          Filter.atTop (nhds (0 : l1Space S)) :=
      (tendsto_zero_iff_norm_tendsto_zero).2 ha
    let g : Nat → l1Space S := fun n =>
      ofL1 (WithLp.ofLp (xn (nk n)) ᵥ* P) - xn (nk n)
    have hxa' : Filter.Tendsto g Filter.atTop (nhds (0 : l1Space S)) := by
      convert hxa using 1
      funext n
      simp [xn, g, Matrix.OfL1.eq.Sub]
    have hb : Filter.Tendsto g Filter.atTop
        (nhds (ofL1 (WithLp.ofLp mul1 ᵥ* P) - mul1)) := by
      have hcont := Matrix.VecMul.Continuous (S := S) P
      exact ((hcont.tendsto mul1).comp hnk_lim).sub hnk_lim
    have hzero : ofL1 (WithLp.ofLp mul1 ᵥ* P) - mul1 = 0 :=
      tendsto_nhds_unique (f := g) hb hxa'
    have : ofL1 (WithLp.ofLp mul1 ᵥ* P) = ofL1 (WithLp.ofLp mul1) := by
      have hmu : mul1 = ofL1 (WithLp.ofLp mul1) := by simp [ofL1]
      rw [← hmu]
      exact sub_eq_zero.mp hzero
    exact (WithLp.toLp_injective (1 : ENNReal)) this

-- created on 2026-09-22
