import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.Sequences
import Mathlib.Topology.Instances.Matrix
import sympy.stats.stochastic_process_types
import sympy.stats.stochastic_process_topology
import sympy.stats.stochastic_process_operator
import sympy.stats.stochastic_process_minorization
import Lemma.Matrix.Stationary.of.Stationary.Pow
import Lemma.Matrix.VecMulSum.eq.Sum_VecMul
import Lemma.Matrix.VecMulSMul.eq.SMul_VecMul
import Lemma.Matrix.L1Norm.eq.One.of.StochasticVec
open Finset WithLp Matrix Filter Metric Topology StochasticMatrix Function PiLp
open scoped Matrix BigOperators Topology NNReal

set_option maxHeartbeats 800000

namespace StochasticMatrix

universe u
variable {S : Type u} [Fintype S] [DecidableEq S]

theorem pos_of_stationary (μ : S → ℝ) [StochasticVec μ]
    (P : Matrix S S ℝ) [RowStochastic P] [StochasticIrreducible P]
    [Stationary μ P] :
    ∀ s, 0 < μ s := by
  by_contra h
  push_neg at h
  set s := h.choose
  have hmu := (inferInstance : StochasticVec μ)
  have hs : μ s = 0 := by
    have := hmu.nonneg s
    linarith [h.choose_spec]
  have hmu0 : ∀ s', μ s' = 0 := by
    intro s'
    obtain ⟨n, hn⟩ :=
      (inferInstance : StochasticIrreducible P).irreducible s' s
    have hPn := (Matrix.Stationary.of.Stationary.Pow μ P n).stationary
    have hfun := congrFun hPn s
    simp [Matrix.vecMul, dotProduct] at hfun
    rw [hs] at hfun
    have hsum0 :=
      (sum_eq_zero_iff_of_nonneg (fun i _ =>
        mul_nonneg (hmu.nonneg i)
          ((RowStochastic.stochastic (P := P ^ n) i).nonneg s))).mp
        hfun s' (mem_univ _)
    exact (or_iff_left (ne_of_gt hn)).mp (by simpa using hsum0)
  have := hmu.rowsum
  simp_rw [hmu0] at this
  simp at this


lemma cesaro_average_is_svec (x0 : S → ℝ) [StochasticVec x0]
    (P : Matrix S S ℝ) [RowStochastic P] (n : ℕ) :
    StochasticVec (cesaro_average x0 P n) := by
  constructor
  · intro i
    have hsumi :
        (∑ k ∈ range (n + 1), x0 ᵥ* P ^ k) i =
          ∑ k ∈ range (n + 1), (x0 ᵥ* P ^ k) i :=
      Finset.sum_apply i (range (n + 1)) (fun k => x0 ᵥ* P ^ k)
    have hnn :
        0 ≤ ∑ k ∈ range (n + 1), (x0 ᵥ* P ^ k) i :=
      sum_nonneg fun k _ => (svec_mul_smat_is_svec x0 (P ^ k)).nonneg i
    simp only [cesaro_average, Pi.smul_apply, smul_eq_mul]
    rw [hsumi]
    exact mul_nonneg (inv_nonneg.mpr (by positivity)) hnn
  · have hterm : ∀ k, StochasticVec (x0 ᵥ* P ^ k) := fun k =>
      svec_mul_smat_is_svec x0 (P ^ k)
    simp only [cesaro_average]
    have hpt : ∀ i,
        ((n + 1 : ℝ)⁻¹ • ∑ k ∈ range (n + 1), x0 ᵥ* P ^ k) i =
          (n + 1 : ℝ)⁻¹ * ∑ k ∈ range (n + 1), (x0 ᵥ* P ^ k) i := by
      intro i; simp [Pi.smul_apply, Finset.sum_apply]
    simp_rw [hpt]
    rw [← mul_sum, sum_comm]
    have hsum :
        ∑ k ∈ range (n + 1), ∑ i, (x0 ᵥ* P ^ k) i = (n + 1 : ℝ) := by
      calc
          ∑ k ∈ range (n + 1), ∑ i, (x0 ᵥ* P ^ k) i
        _ = ∑ k ∈ range (n + 1), (1 : ℝ) := by
            apply sum_congr rfl; intro k _; exact (hterm k).rowsum
        _ = n + 1 := by simp
    rw [hsum]
    field_simp


private lemma ofL1_smul (c : ℝ) (x : S → ℝ) :
    ofL1 (c • x) = c • ofL1 x := by
  ext; simp [ofL1]

private lemma ofL1_sub' (a b : S → ℝ) :
    ofL1 (a - b) = ofL1 a - ofL1 b := by
  ext; simp [ofL1, sub_eq_add_neg]

lemma cesaro_average_almost_invariant (x0 : S → ℝ) [StochasticVec x0]
    (P : Matrix S S ℝ) [RowStochastic P] (n : ℕ) :
    ‖ofL1 (cesaro_average x0 P n ᵥ* P - cesaro_average x0 P n)‖ ≤
      2 / (n + 1) := by
  set c : ℝ := (n + 1 : ℝ)⁻¹
  have hcpos : 0 < c := by unfold c; positivity
  set sk : S → ℝ := ∑ k ∈ range (n + 1), x0 ᵥ* P ^ k
  have havg : cesaro_average x0 P n = c • sk := rfl
  have hlin :
      (c • sk) ᵥ* P - c • sk = c • (sk ᵥ* P - sk) := by
    simp [sub_eq_add_neg, Matrix.VecMulSMul.eq.SMul_VecMul, smul_add, smul_neg]
  have hskP : sk ᵥ* P = ∑ k ∈ range (n + 1), x0 ᵥ* P ^ (k + 1) := by
    simp only [sk]
    rw [Matrix.VecMulSum.eq.Sum_VecMul]
    refine sum_congr rfl fun k _ => ?_
    rw [Matrix.vecMul_vecMul, ← pow_succ]
  have htel : sk ᵥ* P - sk = x0 ᵥ* P ^ (n + 1) - x0 := by
    rw [hskP, ← sum_sub_distrib]
    simpa [pow_zero, Matrix.vecMul_one] using
      Finset.sum_range_sub (fun k => x0 ᵥ* P ^ k) (n + 1)
  rw [havg, hlin, htel, ofL1_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hcpos]
  haveI := svec_mul_smat_is_svec x0 (P ^ (n + 1))
  have hbound : ‖ofL1 (x0 ᵥ* P ^ (n + 1) - x0)‖ ≤ 2 := by
    calc
        ‖ofL1 (x0 ᵥ* P ^ (n + 1) - x0)‖
      _ = ‖ofL1 (x0 ᵥ* P ^ (n + 1)) - ofL1 x0‖ := by rw [ofL1_sub']
      _ ≤ ‖ofL1 (x0 ᵥ* P ^ (n + 1))‖ + ‖ofL1 x0‖ := norm_sub_le _ _
      _ = 1 + 1 := by simp [Matrix.L1Norm.eq.One.of.StochasticVec]
      _ = 2 := by ring
  calc
      c * ‖ofL1 (x0 ᵥ* P ^ (n + 1) - x0)‖
    _ ≤ c * 2 := mul_le_mul_of_nonneg_left hbound hcpos.le
    _ = 2 / (n + 1) := by unfold c; field_simp


instance [Nonempty S] : Nonempty (↑(Simplex S)) :=
  ⟨ofL1 (uniform_distribution (S := S)), by
    simpa [ofL1] using (uniform_distribution_stochastic (S := S))⟩

lemma continuous_vecMul_l1 (P : Matrix S S ℝ) :
    Continuous fun v : l1Space S => ofL1 (WithLp.ofLp v ᵥ* P) := by
  have h1 : Continuous (WithLp.ofLp : l1Space S → (S → ℝ)) :=
    continuous_ofLp (p := (1 : ENNReal)) (β := fun _ : S => ℝ)
  have h2 : Continuous fun x : S → ℝ => x ᵥ* P :=
    Continuous.matrix_vecMul continuous_id continuous_const
  have h3 : Continuous (WithLp.toLp (1 : ENNReal) : (S → ℝ) → l1Space S) :=
    continuous_toLp (p := (1 : ENNReal)) (β := fun _ : S => ℝ)
  exact h3.comp (h2.comp h1)

theorem stationary_distribution_exists (P : Matrix S S ℝ) [RowStochastic P]
    [Nonempty S] :
    ∃ μ : S → ℝ, StochasticVec μ ∧ Stationary μ P := by
  let x0 := uniform_distribution (S := S)
  let xn : ℕ → l1Space S := fun n => ofL1 (cesaro_average x0 P n)
  have hx : ∀ n, xn n ∈ Simplex S := by
    intro n
    simpa [xn, ofL1] using cesaro_average_is_svec x0 P n
  obtain ⟨mul1, hmul1, nk, hnk_mono, hnk_lim⟩ :=
    IsCompact.tendsto_subseq (simples_is_compact (S := S)) hx
  refine ⟨WithLp.ofLp mul1, hmul1, ⟨?hstat⟩⟩
  case hstat =>
    have hbound :
        ∀ n, ‖ofL1 (cesaro_average x0 P (nk n) ᵥ* P -
          cesaro_average x0 P (nk n))‖ ≤ 2 / (nk n + 1 : ℝ) :=
      fun n => cesaro_average_almost_invariant x0 P (nk n)
    have ha :
        Tendsto (fun n =>
          ‖ofL1 (cesaro_average x0 P (nk n) ᵥ* P - cesaro_average x0 P (nk n))‖)
          atTop (nhds (0 : Real)) := by
      refine squeeze_zero (fun _ => norm_nonneg _) hbound ?_
      have hnk_atTop : Tendsto nk atTop atTop := hnk_mono.tendsto_atTop
      have h1 : Tendsto (fun m : Nat => (1 : Real) / (m + 1)) atTop (nhds (0 : Real)) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have hdiv0 :
          Tendsto (fun m : Nat => (2 : Real) * ((1 : Real) / (m + 1))) atTop
            (nhds (0 : Real)) := by
        simpa using (h1.const_mul (2 : Real))
      have hdiv0' :
          Tendsto (fun m : Nat => (2 : Real) / (m + 1)) atTop (nhds (0 : Real)) := by
        convert hdiv0 using 1
        funext m
        ring
      exact hdiv0'.comp hnk_atTop
    have hxa :
        Tendsto (fun n =>
          ofL1 (cesaro_average x0 P (nk n) ᵥ* P - cesaro_average x0 P (nk n)))
          atTop (nhds (0 : l1Space S)) :=
      (tendsto_zero_iff_norm_tendsto_zero).2 ha
    let g : Nat → l1Space S := fun n =>
      ofL1 (WithLp.ofLp (xn (nk n)) ᵥ* P) - xn (nk n)
    have hxa' : Tendsto g atTop (nhds (0 : l1Space S)) := by
      convert hxa using 1
      funext n
      simp [xn, ofL1_sub', g]
    have hb : Tendsto g atTop
        (nhds (ofL1 (WithLp.ofLp mul1 ᵥ* P) - mul1)) := by
      have hcont := continuous_vecMul_l1 (S := S) P
      exact ((hcont.tendsto mul1).comp hnk_lim).sub hnk_lim
    have hzero : ofL1 (WithLp.ofLp mul1 ᵥ* P) - mul1 = 0 :=
      tendsto_nhds_unique (f := g) hb hxa'
    have : ofL1 (WithLp.ofLp mul1 ᵥ* P) = ofL1 (WithLp.ofLp mul1) := by
      have hmu : mul1 = ofL1 (WithLp.ofLp mul1) := by simp [ofL1]
      rw [← hmu]
      exact sub_eq_zero.mp hzero
    exact (WithLp.toLp_injective (1 : ENNReal)) this

theorem stationary_distribution_uniquely_exists (P : Matrix S S ℝ)
    [RowStochastic P] [Aperiodic P] [StochasticIrreducible P] [Nonempty S] :
    ∃! μ : S → ℝ, StochasticVec μ ∧ Stationary μ P := by
  obtain ⟨μ, hmu, hmustat⟩ := stationary_distribution_exists P
  refine ⟨μ, ⟨hmu, hmustat⟩, ?huniq⟩
  intro nu hnu
  obtain ⟨hnu, hnustat⟩ := hnu
  obtain ⟨N0, hNge, hN⟩ := smat_minorizable_with_large_pow P
  let f := smat_as_operator (P ^ N0)
  obtain ⟨K, _, hf⟩ := smat_contraction_in_simplex (P ^ N0)
  have hmufix : IsFixedPt f ⟨ofL1 μ, by simpa [ofL1] using hmu⟩ := by
    change smat_as_operator (P ^ N0) _ = _
    apply Subtype.ext
    simp [smat_as_operator, ofL1]
    exact (Matrix.Stationary.of.Stationary.Pow μ P N0).stationary
  have hnufix : IsFixedPt f ⟨ofL1 nu, by simpa [ofL1] using hnu⟩ := by
    change smat_as_operator (P ^ N0) _ = _
    apply Subtype.ext
    simp [smat_as_operator, ofL1]
    exact (Matrix.Stationary.of.Stationary.Pow nu P N0).stationary
  have := (hf.fixedPoint_unique hnufix).trans (hf.fixedPoint_unique hmufix).symm
  simpa [ofL1] using
    congrArg (fun z : ↑(Simplex S) => WithLp.ofLp (z : l1Space S)) this

end StochasticMatrix
