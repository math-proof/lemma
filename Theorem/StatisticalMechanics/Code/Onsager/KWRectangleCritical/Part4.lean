/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWRectangleCritical.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.KWSpectralCritical
import Def.StatisticalMechanics.Code.Onsager.KWRectangleCritical.Part5


namespace StatMech.Onsager

open Matrix BigOperators

open scoped Matrix.Norms.L2Operator


theorem norm_ons_rectDartMask_le (M N : Nat) :
    letI : NormedRing
        (Matrix (ons_RectDart M N) (ons_RectDart M N) Complex) :=
      Matrix.instL2OpNormedRing
    ‖ons_rectDartMask M N‖ <= 1 := by
  letI : NormedRing
      (Matrix (ons_RectDart M N) (ons_RectDart M N) Complex) :=
    Matrix.instL2OpNormedRing
  rw [ons_rectDartMask, Matrix.l2_opNorm_diagonal]
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro d
  by_cases h : ons_rectDartValid M N d <;> simp [h]


theorem norm_ons_rectKWmat_sharp (M N : Nat) (x : Complex) :
    letI : NormedRing
        (Matrix (ons_RectDart M N) (ons_RectDart M N) Complex) :=
      Matrix.instL2OpNormedRing
    ‖ons_rectKWmat M N x‖ <= (Real.sqrt 2 + 1) * ‖x‖ := by
  letI : NormedRing
      (Matrix (ons_RectDart M N) (ons_RectDart M N) Complex) :=
    Matrix.instL2OpNormedRing
  unfold ons_rectKWmat
  rw [norm_smul]
  calc
    ‖x‖ * ‖ons_rectDartMask M N *
        ons_arrivalTurnMatrixOf (ons_RectVertex M N) *
        (ons_rectTailDartEquiv M N).permMatrix Complex *
        ons_rectDartMask M N‖ <=
      ‖x‖ * (‖ons_rectDartMask M N‖ *
        ‖ons_arrivalTurnMatrixOf (ons_RectVertex M N)‖ *
        ‖(ons_rectTailDartEquiv M N).permMatrix Complex‖ *
        ‖ons_rectDartMask M N‖) := by
          gcongr
          exact (Matrix.l2_opNorm_mul _ _).trans <| by
            gcongr
            exact (Matrix.l2_opNorm_mul _ _).trans <| by
              gcongr
              exact Matrix.l2_opNorm_mul _ _
    _ <= ‖x‖ * (1 * (Real.sqrt 2 + 1) * 1 * 1) := by
      gcongr
      · exact norm_ons_rectDartMask_le M N
      · exact norm_ons_arrivalTurnMatrixOf_le (ons_RectVertex M N)
      · exact Matrix.permMatrix_l2_opNorm_le _
      · exact norm_ons_rectDartMask_le M N
    _ = (Real.sqrt 2 + 1) * ‖x‖ := by ring

theorem ons_rectDartMask_apply (M N : Nat)
    (z : EuclideanSpace Complex (ons_RectDart M N))
    (d : ons_RectDart M N) :
    (Matrix.toEuclideanCLM (n := ons_RectDart M N) (𝕜 := Complex)
      (ons_rectDartMask M N) z).ofLp d =
      if ons_rectDartValid M N d then z.ofLp d else 0 := by
  rw [Matrix.ofLp_toEuclideanCLM]
  simp [ons_rectDartMask, Matrix.mulVec_diagonal]

theorem ons_rectTailPerm_apply (M N : Nat)
    (z : EuclideanSpace Complex (ons_RectDart M N))
    (d : ons_RectDart M N) :
    (Matrix.toEuclideanCLM (n := ons_RectDart M N) (𝕜 := Complex)
      ((ons_rectTailDartEquiv M N).permMatrix Complex) z).ofLp d =
      z.ofLp (ons_rectTailDartEquiv M N d) := by
  rw [Matrix.ofLp_toEuclideanCLM, Matrix.permMatrix_mulVec]
  rfl

theorem norm_ons_rectTailPerm_apply (M N : Nat)
    (z : EuclideanSpace Complex (ons_RectDart M N)) :
    ‖Matrix.toEuclideanCLM (n := ons_RectDart M N) (𝕜 := Complex)
      ((ons_rectTailDartEquiv M N).permMatrix Complex) z‖ = ‖z‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  rw [Matrix.ofLp_toEuclideanCLM, Matrix.permMatrix_mulVec]
  exact Equiv.sum_comp (ons_rectTailDartEquiv M N)
    (fun i => ‖z.ofLp i‖ ^ 2)

theorem ons_rectKWmat_toEuclideanCLM_apply (M N : Nat) (x : Complex)
    (z : EuclideanSpace Complex (ons_RectDart M N)) :
    Matrix.toEuclideanCLM (n := ons_RectDart M N) (𝕜 := Complex)
        (ons_rectKWmat M N x) z =
      x • Matrix.toEuclideanCLM (n := ons_RectDart M N) (𝕜 := Complex)
        (ons_rectDartMask M N)
        (Matrix.toEuclideanCLM (n := ons_RectDart M N) (𝕜 := Complex)
          (ons_arrivalTurnMatrixOf (ons_RectVertex M N))
          (Matrix.toEuclideanCLM (n := ons_RectDart M N) (𝕜 := Complex)
            ((ons_rectTailDartEquiv M N).permMatrix Complex)
            (Matrix.toEuclideanCLM (n := ons_RectDart M N) (𝕜 := Complex)
              (ons_rectDartMask M N) z))) := by
  simp [ons_rectKWmat, map_mul]


theorem rectDartVector_eq_zero_of_recurrence (M N : Nat)
    (alpha : Complex) (halpha : alpha ≠ 0)
    (z : EuclideanSpace Complex (ons_RectDart M N))
    (hboundary : ∀ d, ¬ons_rectDartValid M N d -> z.ofLp d = 0)
    (hrec : ∀ d, ons_rectDartValid M N d ->
      alpha * z.ofLp d = z.ofLp (ons_rectTailDartEquiv M N d)) :
    z = 0 := by
  apply (EuclideanSpace.equiv (ons_RectDart M N) Complex).injective
  funext d
  change z.ofLp d = 0
  refine @WellFounded.induction _ _
    (measure (ons_rectDartBoundaryRank M N)).wf
    (fun d => z.ofLp d = 0) d ?_
  intro d ih
  by_cases hd : ons_rectDartValid M N d
  · have htailzero : z.ofLp (ons_rectTailDartEquiv M N d) = 0 := by
      by_cases htail : ons_rectDartValid M N (ons_rectTailDartEquiv M N d)
      · exact ih (ons_rectTailDartEquiv M N d)
          (ons_rectDartBoundaryRank_tail_lt M N d hd htail)
      · exact hboundary _ htail
    have hmul : alpha * z.ofLp d = 0 := by rw [hrec d hd, htailzero]
    exact (mul_eq_zero.mp hmul).resolve_left halpha
  · exact hboundary d hd


theorem ons_rectKWmat_no_unit_eigenvector (M N : Nat)
    (alpha : Complex) (v : EuclideanSpace Complex (ons_RectDart M N))
    (hunit : ‖alpha‖ = 1)
    (heigen : Matrix.toEuclideanCLM
      (n := ons_RectDart M N) (𝕜 := Complex)
      (ons_rectKWmat M N (ons_signedLoopCriticalWeight : Complex)) v =
        alpha • v) :
    v = 0 := by
  let q := ons_signedLoopCriticalWeight
  let c := Real.sqrt 2 + 1
  let D := Matrix.toEuclideanCLM
    (n := ons_RectDart M N) (𝕜 := Complex) (ons_rectDartMask M N)
  let R := Matrix.toEuclideanCLM
    (n := ons_RectDart M N) (𝕜 := Complex)
      (ons_arrivalTurnMatrixOf (ons_RectVertex M N))
  let P := Matrix.toEuclideanCLM
    (n := ons_RectDart M N) (𝕜 := Complex)
      ((ons_rectTailDartEquiv M N).permMatrix Complex)
  let A := Matrix.toEuclideanCLM
    (n := ons_RectDart M N) (𝕜 := Complex)
      (ons_rectKWmat M N (q : Complex))
  have hqpos : 0 < q := ons_signedLoopCriticalWeight_pos
  have hcpos : 0 < c := by dsimp [c]; positivity
  have hqc : q * c = 1 := by
    dsimp [q, c]
    rw [mul_comm]
    exact sqrt_two_add_one_mul_signedLoopCriticalWeight
  have halpha : alpha ≠ 0 := by
    exact norm_ne_zero_iff.mp (by rw [hunit]; norm_num)
  have hboundary : ∀ d, ¬ons_rectDartValid M N d -> v.ofLp d = 0 := by
    intro d hd
    have hAzero : (A v).ofLp d = 0 := by
      have h := congrArg (fun w => w.ofLp d)
        (ons_rectKWmat_toEuclideanCLM_apply M N
          (ons_signedLoopCriticalWeight : Complex) v)
      calc
        (A v).ofLp d =
            ((ons_signedLoopCriticalWeight : Complex) •
              Matrix.toEuclideanCLM
                (n := ons_RectDart M N) (𝕜 := Complex)
                (ons_rectDartMask M N)
                (Matrix.toEuclideanCLM
                  (n := ons_RectDart M N) (𝕜 := Complex)
                  (ons_arrivalTurnMatrixOf (ons_RectVertex M N))
                  (Matrix.toEuclideanCLM
                    (n := ons_RectDart M N) (𝕜 := Complex)
                    ((ons_rectTailDartEquiv M N).permMatrix Complex)
                    (Matrix.toEuclideanCLM
                      (n := ons_RectDart M N) (𝕜 := Complex)
                      (ons_rectDartMask M N) v)))).ofLp d := by
                        simpa [A, q] using h
        _ = 0 := by
          simp only [PiLp.smul_apply]
          rw [ons_rectDartMask_apply]
          simp [hd]
    have hcoord := congrArg (fun w => w.ofLp d) heigen
    change (A v).ofLp d = (alpha • v).ofLp d at hcoord
    rw [hAzero] at hcoord
    simp only [PiLp.smul_apply] at hcoord
    exact (mul_eq_zero.mp hcoord.symm).resolve_left halpha
  have hDv : D v = v := by
    apply (EuclideanSpace.equiv (ons_RectDart M N) Complex).injective
    funext d
    change (D v).ofLp d = v.ofLp d
    rw [show D = Matrix.toEuclideanCLM
      (n := ons_RectDart M N) (𝕜 := Complex)
      (ons_rectDartMask M N) by rfl]
    rw [ons_rectDartMask_apply]
    by_cases hd : ons_rectDartValid M N d
    · simp [hd]
    · simp [hd, hboundary d hd]
  let z := P (D v)
  let y := R z
  have hz : ‖z‖ = ‖v‖ := by
    dsimp [z, P]
    rw [norm_ons_rectTailPerm_apply, hDv]
  have hAaction : A v = (q : Complex) • D y := by
    dsimp [A, y, z, R, P, D, q]
    exact ons_rectKWmat_toEuclideanCLM_apply M N
      (ons_signedLoopCriticalWeight : Complex) v
  have hAvnorm : ‖A v‖ = ‖v‖ := by
    change ‖Matrix.toEuclideanCLM
      (n := ons_RectDart M N) (𝕜 := Complex)
      (ons_rectKWmat M N (ons_signedLoopCriticalWeight : Complex)) v‖ = ‖v‖
    rw [heigen, norm_smul, hunit, one_mul]
  have hDnorm : ‖D‖ <= 1 := by
    exact norm_ons_rectDartMask_le M N
  have hD_apply (w : EuclideanSpace Complex (ons_RectDart M N)) :
      ‖D w‖ <= ‖w‖ := by
    calc
      ‖D w‖ <= ‖D‖ * ‖w‖ := D.le_opNorm w
      _ <= 1 * ‖w‖ := mul_le_mul_of_nonneg_right hDnorm (norm_nonneg _)
      _ = ‖w‖ := one_mul _
  have hRnorm : ‖R‖ <= c := by
    exact norm_ons_arrivalTurnMatrixOf_le (ons_RectVertex M N)
  have hR_apply : ‖y‖ <= c * ‖z‖ := by
    dsimp [y]
    exact (R.le_opNorm z).trans <|
      mul_le_mul_of_nonneg_right hRnorm (norm_nonneg _)
  have hAv_formula : ‖A v‖ = q * ‖D y‖ := by
    rw [hAaction, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hqpos]
  have hlower : ‖v‖ <= q * ‖y‖ := by
    calc
      ‖v‖ = ‖A v‖ := hAvnorm.symm
      _ = q * ‖D y‖ := hAv_formula
      _ <= q * ‖y‖ := mul_le_mul_of_nonneg_left (hD_apply y) hqpos.le
  have hlowerR : c * ‖z‖ <= ‖y‖ := by
    have hmul : q * (c * ‖z‖) <= q * ‖y‖ := calc
      q * (c * ‖z‖) = ‖v‖ := by rw [← mul_assoc, hqc, one_mul, hz]
      _ <= q * ‖y‖ := hlower
    exact le_of_mul_le_mul_left hmul hqpos
  have hRsharp : ‖y‖ = c * ‖z‖ := le_antisymm hR_apply hlowerR
  have htop : R z = (c : Complex) • z := by
    dsimp [R, c]
    apply arrivalTurnMatrixOf_apply_eq_of_norm_eq (ons_RectVertex M N) z
    simpa [y, c] using hRsharp
  have hrec : ∀ d, ons_rectDartValid M N d ->
      alpha * v.ofLp d = v.ofLp (ons_rectTailDartEquiv M N d) := by
    intro d hd
    have hcoord := congrArg (fun w => w.ofLp d) heigen
    change (A v).ofLp d = (alpha • v).ofLp d at hcoord
    rw [hAaction, show y = R z by rfl, htop] at hcoord
    have hDcoord : (D ((c : Complex) • z)).ofLp d =
        (c : Complex) * z.ofLp d := by
      calc
        (D ((c : Complex) • z)).ofLp d =
            if ons_rectDartValid M N d then
              ((c : Complex) • z).ofLp d else 0 := by
                simpa [D] using
                  ons_rectDartMask_apply M N ((c : Complex) • z) d
        _ = (c : Complex) * z.ofLp d := by simp [hd]
    simp only [PiLp.smul_apply] at hcoord
    rw [hDcoord] at hcoord
    have hzcoord : z.ofLp d = v.ofLp (ons_rectTailDartEquiv M N d) := by
      calc
        z.ofLp d = (P (D v)).ofLp d := rfl
        _ = (D v).ofLp (ons_rectTailDartEquiv M N d) := by
          simpa [P] using ons_rectTailPerm_apply M N (D v) d
        _ = v.ofLp (ons_rectTailDartEquiv M N d) := by rw [hDv]
    change (q : Complex) * ((c : Complex) * z.ofLp d) =
      alpha * v.ofLp d at hcoord
    have hqcC : (q : Complex) * (c : Complex) = 1 := by exact_mod_cast hqc
    calc
      alpha * v.ofLp d = (q : Complex) * ((c : Complex) * z.ofLp d) :=
        hcoord.symm
      _ = z.ofLp d := by rw [← mul_assoc, hqcC, one_mul]
      _ = v.ofLp (ons_rectTailDartEquiv M N d) := hzcoord
  exact rectDartVector_eq_zero_of_recurrence M N alpha halpha v hboundary hrec


theorem norm_root_ons_rectKWmat_le (M N : Nat) (x alpha : Complex)
    (halpha : alpha ∈ (ons_rectKWmat M N x).charpoly.roots) :
    ‖alpha‖ <= (Real.sqrt 2 + 1) * ‖x‖ := by
  letI : NormedRing
      (Matrix (ons_RectDart M N) (ons_RectDart M N) Complex) :=
    Matrix.instL2OpNormedRing
  let A := ons_rectKWmat M N x
  have hroot : A.charpoly.IsRoot alpha :=
    (Polynomial.mem_roots (Matrix.charpoly_monic A).ne_zero).mp halpha
  have heig : Module.End.HasEigenvalue (Matrix.toLin' A) alpha :=
    (Module.End.hasEigenvalue_iff_isRoot_charpoly (Matrix.toLin' A) alpha).2 <| by
      rw [Matrix.charpoly_toLin']
      exact hroot
  obtain ⟨v, hv⟩ := heig.exists_hasEigenvector
  let vE : EuclideanSpace Complex (ons_RectDart M N) :=
    (EuclideanSpace.equiv (ons_RectDart M N) Complex).symm v
  have hvE : vE ≠ 0 := by
    intro hzero
    apply hv.2
    apply (EuclideanSpace.equiv (ons_RectDart M N) Complex).symm.injective
    simpa [vE] using hzero
  have heigen :
      (EuclideanSpace.equiv (ons_RectDart M N) Complex).symm (A *ᵥ vE) =
        alpha • vE := by
    apply (EuclideanSpace.equiv (ons_RectDart M N) Complex).injective
    simpa [vE, Matrix.toLin'_apply] using hv.apply_eq_smul
  have hmul : ‖alpha‖ * ‖vE‖ <= ‖A‖ * ‖vE‖ := by
    rw [← norm_smul, ← heigen]
    exact Matrix.l2_opNorm_mulVec A vE
  have halpha_le : ‖alpha‖ <= ‖A‖ :=
    le_of_mul_le_mul_right hmul (norm_pos_iff.mpr hvE)
  exact halpha_le.trans (norm_ons_rectKWmat_sharp M N x)


theorem ons_rectKWmat_spectral_critical (M N : Nat) :
    ∀ alpha ∈
      (ons_rectKWmat M N
        (ons_signedLoopCriticalWeight : Complex)).charpoly.roots,
      ‖alpha‖ < 1 := by
  intro alpha halpha
  have hle : ‖alpha‖ <= 1 := by
    have h := norm_root_ons_rectKWmat_le M N
      (ons_signedLoopCriticalWeight : Complex) alpha halpha
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ons_signedLoopCriticalWeight_pos,
      sqrt_two_add_one_mul_signedLoopCriticalWeight] at h
    exact h
  apply lt_of_le_of_ne hle
  intro hunit
  let A := ons_rectKWmat M N (ons_signedLoopCriticalWeight : Complex)
  have hroot : A.charpoly.IsRoot alpha :=
    (Polynomial.mem_roots (Matrix.charpoly_monic A).ne_zero).mp halpha
  have heig : Module.End.HasEigenvalue (Matrix.toLin' A) alpha :=
    (Module.End.hasEigenvalue_iff_isRoot_charpoly (Matrix.toLin' A) alpha).2 <| by
      rw [Matrix.charpoly_toLin']
      exact hroot
  obtain ⟨v, hv⟩ := heig.exists_hasEigenvector
  let vE : EuclideanSpace Complex (ons_RectDart M N) :=
    (EuclideanSpace.equiv (ons_RectDart M N) Complex).symm v
  have hvE : vE ≠ 0 := by
    intro hzero
    apply hv.2
    apply (EuclideanSpace.equiv (ons_RectDart M N) Complex).symm.injective
    simpa [vE] using hzero
  have heigen : Matrix.toEuclideanCLM
      (n := ons_RectDart M N) (𝕜 := Complex) A vE = alpha • vE := by
    apply (EuclideanSpace.equiv (ons_RectDart M N) Complex).injective
    simpa [vE, Matrix.toLin'_apply] using hv.apply_eq_smul
  exact hvE (ons_rectKWmat_no_unit_eigenvector M N alpha vE hunit heigen)


theorem ons_rectKWmat_det_eq_walk_exp_critical (M N : Nat) :
    (1 - ons_rectKWmat M N
      (ons_signedLoopCriticalWeight : Complex)).det =
      Complex.exp (- ∑' n : Nat,
        (∑ v : Fin (n + 1) -> ons_RectDart M N,
          ∏ k : Fin (n + 1),
            ons_rectKWmat M N (ons_signedLoopCriticalWeight : Complex)
              (v k) (v (k + 1))) / (n + 1)) := by
  exact ons_det_eq_walk_exp _ (ons_rectKWmat_spectral_critical M N)

end StatMech.Onsager
