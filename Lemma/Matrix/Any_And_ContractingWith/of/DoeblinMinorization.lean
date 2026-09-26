import Lemma.Matrix.VecMul_SMul.eq.SMul_VecMul
import Lemma.Matrix.VecMul_Broadcast.eq.FunMulSum
import Lemma.Matrix.LeNormOfL1SubVecMulS.of.RowStochastic
import Lemma.Matrix.OfL1.eq.SMul
import Lemma.Matrix.OfL1.eq.Sub
import Lemma.Real.Nndist.eq.NormOfL1Sub
open WithLp Matrix Metric NNReal Real
open scoped Matrix BigOperators Topology NNReal


@[main]
private lemma main
  {S : Type u} [Fintype S]
  {P : Matrix S S ℝ} [RowStochastic P]
-- given
  (h : DoeblinMinorization P) :
-- imply
  ∃ K, 0 < K ∧ ContractingWith K (smat_as_operator P) := by
-- proof
  obtain ⟨ε, ν, hεpos, hεlt1, hν, hmin⟩ := h.minorize
  have hε0 : 0 ≤ 1 - ε := by grind
  have hnonzero : 1 - ε ≠ 0 := by grind
  let Q := (1 - ε)⁻¹ • (P - ε • broadcast ν)
  have h_decomp : P = ε • broadcast ν + (1 - ε) • Q := by
    unfold Q
    simp [hnonzero]
  let K : ℝ≥0 := ⟨1 - ε, hε0⟩
  refine ⟨K, ⟨?_, ⟨?_, ?_⟩⟩⟩
  ·
    exact_mod_cast (by grind : 0 < 1 - ε)
  ·
    change (1 - ε : ℝ) < 1
    grind
  ·
    intro x y
    set xv : S → ℝ := WithLp.ofLp (x : l1Space S)
    set yv : S → ℝ := WithLp.ofLp (y : l1Space S)
    have hxB : xv ᵥ* broadcast ν = ν := by
      rw [VecMul_Broadcast.eq.FunMulSum]
      funext j
      simp [xv, x.property.rowsum]
    have hyB : yv ᵥ* broadcast ν = ν := by
      rw [VecMul_Broadcast.eq.FunMulSum]
      funext j
      simp [yv, y.property.rowsum]
    have hxP : xv ᵥ* P = ε • (xv ᵥ* broadcast ν) + (1 - ε) • (xv ᵥ* Q) := by
      rw [h_decomp]
      simp [vecMul_add, VecMul_SMul.eq.SMul_VecMul]
    have hyP : yv ᵥ* P = ε • (yv ᵥ* broadcast ν) + (1 - ε) • (yv ᵥ* Q) := by
      rw [h_decomp]
      simp [vecMul_add, VecMul_SMul.eq.SMul_VecMul]
    rw [edist_nndist, edist_nndist, ← ENNReal.coe_mul]
    apply ENNReal.coe_le_coe.mpr
    have hL : (nndist (smat_as_operator P x : l1Space S) (smat_as_operator P y : l1Space S) : ℝ) = ‖ofL1 (xv ᵥ* P - yv ᵥ* P)‖ := by
      change (nndist (WithLp.toLp 1 (xv ᵥ* P)) (WithLp.toLp 1 (yv ᵥ* P)) : ℝ) = _
      simpa [ofL1] using Nndist.eq.NormOfL1Sub (xv ᵥ* P) (yv ᵥ* P)
    have hR : (nndist (x : l1Space S) (y : l1Space S) : ℝ) = ‖ofL1 (xv - yv)‖ := by
      rw [show (x : l1Space S) = ofL1 xv by simp [xv, ofL1], show (y : l1Space S) = ofL1 yv by simp [yv, ofL1]]
      apply Nndist.eq.NormOfL1Sub
    apply NNReal.coe_le_coe.mp
    rw [NNReal.coe_mul]
    change (nndist (smat_as_operator P x : l1Space S) (smat_as_operator P y : l1Space S) : ℝ) ≤ (K : ℝ) * (nndist (x : l1Space S) (y : l1Space S) : ℝ)
    rw [hL, hR]
    calc
      _ = ‖ofL1 ((1 - ε) • (xv ᵥ* Q - yv ᵥ* Q))‖ := by
        rw [hxP, hyP, hxB, hyB]
        congr 1
        ext j
        simp [Pi.sub_apply, Pi.smul_apply]
        ring
      _ = (1 - ε) * ‖ofL1 (xv ᵥ* Q - yv ᵥ* Q)‖ := by
        rw [OfL1.eq.SMul, norm_smul, norm_eq_abs, abs_of_nonneg hε0]
      _ ≤ (1 - ε) * ‖ofL1 (xv - yv)‖ := by
        refine mul_le_mul_of_nonneg_left (LeNormOfL1SubVecMulS.of.RowStochastic ?_ xv yv) hε0
        constructor
        intro i
        constructor
        · intro j
          have hmul := mul_nonneg (inv_nonneg.mpr hε0) (sub_nonneg.mpr (hmin i j))
          simpa [Q, broadcast, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul] using hmul
        · have hP := (inferInstance : RowStochastic P).stochastic i
          calc
            _ = ∑ j, (1 - ε)⁻¹ * (P i j - ε * ν j) := by
              apply Finset.sum_congr rfl
              intro j _
              simp [Q, broadcast, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
            _ = (1 - ε)⁻¹ * ∑ j, (P i j - ε * ν j) := by
              rw [Finset.mul_sum]
            _ = (1 - ε)⁻¹ * (∑ j, P i j - ∑ j, ε * ν j) := by
              rw [Finset.sum_sub_distrib]
            _ = (1 - ε)⁻¹ * (1 - ε * ∑ j, ν j) := by
              rw [hP.rowsum, Finset.mul_sum]
            _ = (1 - ε)⁻¹ * (1 - ε) := by
              rw [hν.rowsum, mul_one]
            _ = 1 := by
              field_simp [hnonzero]
      _ = (K : ℝ) * ‖ofL1 (xv - yv)‖ := rfl


-- created on 2026-09-22
-- updated on 2026-09-24
