import Mathlib.Topology.MetricSpace.Contracting
import sympy.stats.stochastic_process_types
import sympy.stats.stochastic_process_topology
import Lemma.Matrix.VecMul_SMul.eq.SMul_VecMul
import Lemma.Matrix.VecMulBroadcast.eq.Mul_Sum
import Lemma.Matrix.Le_L1Norm.of.RowStochastic
import Lemma.Matrix.Le_L1Norm.of.RowStochastic.Pow
open Finset WithLp Matrix Metric ENNReal NNReal StochasticMatrix
open scoped Matrix BigOperators Topology NNReal

namespace StochasticMatrix

universe u
variable {S : Type u} [Fintype S]

noncomputable def smat_as_operator (P : Matrix S S ℝ) [RowStochastic P] :
    ↑(Simplex S) → ↑(Simplex S) :=
  fun μ =>
    ⟨WithLp.toLp 1 (WithLp.ofLp (μ : l1Space S) ᵥ* P), by
      have : StochasticVec (WithLp.ofLp (μ : l1Space S) ᵥ* P) :=
        inferInstance
      simpa using this⟩

lemma smat_as_operator_apply (P : Matrix S S ℝ) [RowStochastic P] (μ : ↑(Simplex S)) :
    (smat_as_operator P μ : l1Space S) =
      WithLp.toLp 1 (WithLp.ofLp (μ : l1Space S) ᵥ* P) :=
  rfl

lemma smat_as_operator_iter [DecidableEq S]
    (P : Matrix S S ℝ) [RowStochastic P] (n : ℕ) (μ : ↑(Simplex S)) :
    ((smat_as_operator P)^[n] μ : l1Space S) =
      WithLp.toLp 1 (WithLp.ofLp (μ : l1Space S) ᵥ* (P ^ n)) := by
  induction n generalizing μ with
  | zero =>
    simp [smat_as_operator]
  | succ n ih =>
    rw [Function.iterate_succ_apply', smat_as_operator_apply, ih]
    simp [pow_succ, WithLp.ofLp_toLp, Matrix.vecMul_vecMul]

theorem smat_nonexpansive_in_l1 (Q : Matrix S S ℝ) [RowStochastic Q]
    (x y : S → ℝ) :
    ‖ofL1 (x ᵥ* Q - y ᵥ* Q)‖ ≤ ‖ofL1 (x - y)‖ :=
  Matrix.Le_L1Norm.of.RowStochastic Q x y

theorem smat_pow_nonexpansive_in_l1 [DecidableEq S]
    (Q : Matrix S S ℝ) [RowStochastic Q] (n : ℕ) (x y : S → ℝ) :
    ‖ofL1 (x ᵥ* Q ^ n - y ᵥ* Q ^ n)‖ ≤ ‖ofL1 (x - y)‖ :=
  Matrix.Le_L1Norm.of.RowStochastic.Pow Q n x y

private lemma ofL1_sub (a b : S → ℝ) :
    ofL1 a - ofL1 b = ofL1 (a - b) := by
  ext s
  simp [ofL1, sub_eq_add_neg]

private lemma nndist_ofL1 (a b : S → ℝ) :
    (nndist (ofL1 a) (ofL1 b) : ℝ) = ‖ofL1 (a - b)‖ := by
  rw [nndist_eq_nnnorm, ofL1_sub, coe_nnnorm]

private lemma subtype_val_eq_ofL1 (x : ↑(Simplex S)) :
    (x : l1Space S) = ofL1 (WithLp.ofLp (x : l1Space S)) := by
  simp [ofL1]

theorem smat_contraction_in_simplex
    (P : Matrix S S ℝ) [RowStochastic P] [DoeblinMinorization P] :
    ∃ K, 0 < K ∧ ContractingWith K (smat_as_operator P) := by
  obtain ⟨ε, ν, hεpos, hεlt1, hν, hmin⟩ :=
    (inferInstance : DoeblinMinorization P).minorize
  have hε0 : 0 ≤ 1 - ε := by linarith
  have hnonzero : 1 - ε ≠ 0 := by linarith
  let Q : Matrix S S ℝ := (1 - ε)⁻¹ • (P - ε • broadcast ν)
  have h_decomp : P = ε • broadcast ν + (1 - ε) • Q := by
    unfold Q; simp [hnonzero]
  have hQ : RowStochastic Q := by
    constructor
    intro i
    constructor
    · intro j
      have hinv : 0 ≤ (1 - ε)⁻¹ := inv_nonneg.mpr hε0
      have hdiff : 0 ≤ P i j - ε * ν j := sub_nonneg.mpr (hmin i j)
      simpa [Q, broadcast, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul] using
        mul_nonneg hinv hdiff
    · have hP := (inferInstance : RowStochastic P).stochastic i
      calc
          ∑ j, Q i j
        _ = ∑ j, (1 - ε)⁻¹ * (P i j - ε * ν j) := by
            apply Finset.sum_congr rfl
            intro j _
            simp [Q, broadcast, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
        _ = (1 - ε)⁻¹ * ∑ j, (P i j - ε * ν j) := by
            rw [mul_sum]
        _ = (1 - ε)⁻¹ * (∑ j, P i j - ∑ j, ε * ν j) := by
            rw [sum_sub_distrib]
        _ = (1 - ε)⁻¹ * (1 - ε * ∑ j, ν j) := by
            rw [hP.rowsum, mul_sum]
        _ = (1 - ε)⁻¹ * (1 - ε) := by
            rw [hν.rowsum, mul_one]
        _ = 1 := by
            field_simp [hnonzero]
  let K : ℝ≥0 := ⟨1 - ε, hε0⟩
  refine ⟨K, ?hKpos, ⟨?hKlt1, ?hLip⟩⟩
  case hKpos =>
    have : 0 < 1 - ε := by linarith
    exact_mod_cast this
  case hKlt1 =>
    have : (1 - ε : ℝ) < 1 := by linarith
    exact this
  case hLip =>
    intro x y
    set xv : S → ℝ := WithLp.ofLp (x : l1Space S)
    set yv : S → ℝ := WithLp.ofLp (y : l1Space S)
    have hx_sum : ∑ i, xv i = 1 := x.property.rowsum
    have hy_sum : ∑ i, yv i = 1 := y.property.rowsum
    have hxB : xv ᵥ* broadcast ν = ν := by
      rw [Matrix.VecMulBroadcast.eq.Mul_Sum]
      funext j
      simp [hx_sum]
    have hyB : yv ᵥ* broadcast ν = ν := by
      rw [Matrix.VecMulBroadcast.eq.Mul_Sum]
      funext j
      simp [hy_sum]
    have hxP :
        xv ᵥ* P = ε • (xv ᵥ* broadcast ν) + (1 - ε) • (xv ᵥ* Q) := by
      rw [h_decomp]
      simp [Matrix.vecMul_add, Matrix.VecMul_SMul.eq.SMul_VecMul]
    have hyP :
        yv ᵥ* P = ε • (yv ᵥ* broadcast ν) + (1 - ε) • (yv ᵥ* Q) := by
      rw [h_decomp]
      simp [Matrix.vecMul_add, Matrix.VecMul_SMul.eq.SMul_VecMul]
    have diff_eq :
        xv ᵥ* P - yv ᵥ* P = (1 - ε) • (xv ᵥ* Q - yv ᵥ* Q) := by
      rw [hxP, hyP, hxB, hyB]
      ext j
      simp [Pi.sub_apply, Pi.add_apply, Pi.smul_apply]
      ring
    have hxynorm :
        ‖ofL1 (xv ᵥ* P - yv ᵥ* P)‖ ≤ (K : ℝ) * ‖ofL1 (xv - yv)‖ := by
      have hsmul :
          ‖ofL1 ((1 - ε) • (xv ᵥ* Q - yv ᵥ* Q))‖ =
            (1 - ε) * ‖ofL1 (xv ᵥ* Q - yv ᵥ* Q)‖ := by
        have heq :
            ofL1 ((1 - ε) • (xv ᵥ* Q - yv ᵥ* Q)) =
              (1 - ε) • ofL1 (xv ᵥ* Q - yv ᵥ* Q) := by
          ext s; simp [ofL1]
        rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg hε0]
      have hLipQ := smat_nonexpansive_in_l1 Q xv yv
      have hKcoe : (K : ℝ) = 1 - ε := rfl
      calc
          ‖ofL1 (xv ᵥ* P - yv ᵥ* P)‖
        _ = ‖ofL1 ((1 - ε) • (xv ᵥ* Q - yv ᵥ* Q))‖ := by rw [diff_eq]
        _ = (1 - ε) * ‖ofL1 (xv ᵥ* Q - yv ᵥ* Q)‖ := hsmul
        _ ≤ (1 - ε) * ‖ofL1 (xv - yv)‖ :=
            mul_le_mul_of_nonneg_left hLipQ hε0
        _ = (K : ℝ) * ‖ofL1 (xv - yv)‖ := by rw [hKcoe]
    have hnndist :
        nndist (smat_as_operator P x) (smat_as_operator P y) ≤
          K * nndist x y := by
      have hL :
          (nndist (smat_as_operator P x : l1Space S)
            (smat_as_operator P y : l1Space S) : ℝ) =
            ‖ofL1 (xv ᵥ* P - yv ᵥ* P)‖ := by
        change (nndist (WithLp.toLp 1 (xv ᵥ* P)) (WithLp.toLp 1 (yv ᵥ* P)) : ℝ) = _
        simpa [ofL1] using nndist_ofL1 (xv ᵥ* P) (yv ᵥ* P)
      have hR :
          (nndist (x : l1Space S) (y : l1Space S) : ℝ) = ‖ofL1 (xv - yv)‖ := by
        have hx : (x : l1Space S) = ofL1 xv := by simp [xv, ofL1]
        have hy : (y : l1Space S) = ofL1 yv := by simp [yv, ofL1]
        rw [hx, hy]
        exact nndist_ofL1 xv yv
      have : (nndist (smat_as_operator P x) (smat_as_operator P y) : ℝ) ≤
          (K : ℝ) * (nndist x y : ℝ) := by
        change (nndist (smat_as_operator P x : l1Space S)
            (smat_as_operator P y : l1Space S) : ℝ) ≤
          (K : ℝ) * (nndist (x : l1Space S) (y : l1Space S) : ℝ)
        rw [hL, hR]
        exact hxynorm
      exact NNReal.coe_le_coe.mp (by simpa [NNReal.coe_mul] using this)
    rw [edist_nndist, edist_nndist, ← ENNReal.coe_mul]
    exact ENNReal.coe_le_coe.mpr hnndist

end StochasticMatrix
