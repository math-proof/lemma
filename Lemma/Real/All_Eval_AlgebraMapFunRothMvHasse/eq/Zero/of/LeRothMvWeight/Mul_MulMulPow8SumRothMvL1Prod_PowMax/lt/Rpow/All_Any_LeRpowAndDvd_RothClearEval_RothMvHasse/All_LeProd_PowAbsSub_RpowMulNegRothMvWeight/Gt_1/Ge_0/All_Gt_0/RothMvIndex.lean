import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
import Lemma.MvPolynomial.RothHelpers
import Lemma.MvPolynomial.EvalAlgebraMap.eq.Eval_AlgebraMapFun
import Lemma.Real.AbsEval.le.MulMulMulPow8SumRothMvL1Prod_PowMaxRpow.of.All_LeProd_PowAbsSub_RpowMulNegRothMvWeight.Ge_1.Ge_0.RothMvIndex.All_Gt_0
open MathlibExt.NumberTheory.RothAuxiliary
open MvPolynomial Real
set_option maxHeartbeats 800000


private lemma denProduct_mul_eval₂_h
  {m : ℕ}
  (P : MvPolynomial (Fin m) ℤ)
  (q : Fin m → ℚ)
  (r : Fin m → ℕ)
-- given
  (hP : rothDegreeBound P r) :
-- imply
  (rothDenProduct q r : ℚ) *
      MvPolynomial.eval₂ (algebraMap ℤ ℚ) q P =
    (rothClearEval P q r : ℚ) := by
-- proof
  classical
  unfold rothDenProduct rothClearEval
  rw [MvPolynomial.eval₂_eq']
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hcoord : ∀ h,
      ((q h).den : ℚ) ^ r h * q h ^ d h =
        ((((q h).num ^ d h * ((q h).den : ℤ) ^ (r h - d h)) : ℤ) : ℚ) := by
    intro h
    have hcast : ((((q h).num ^ d h * ((q h).den : ℤ) ^ (r h - d h)) : ℤ) : ℚ) =
        ((q h).num : ℚ) ^ d h * ((q h).den : ℚ) ^ (r h - d h) := by
      push_cast
      rfl
    rw [hcast]
    calc
      _ = ((q h).den : ℚ) ^ r h *
            (((q h).num : ℚ) / (q h).den) ^ d h := by
        rw [(q h).num_div_den]
      _ = ((q h).num : ℚ) ^ d h *
          ((q h).den : ℚ) ^ (r h - d h) := by
        rw [div_pow]
        have hden : ((q h).den : ℚ) ≠ 0 := by
          exact_mod_cast (q h).den_nz
        field_simp
        have hp : ((q h).den : ℚ) ^ r h =
            ((q h).den : ℚ) ^ d h *
              ((q h).den : ℚ) ^ (r h - d h) := by
          rw [← pow_add, Nat.add_sub_of_le (hP d hd h)]
        rw [hp]
        ring
  have hfactor : (∏ h, ((q h).den : ℚ) ^ r h) *
      ((algebraMap ℤ ℚ) (P.coeff d) * ∏ h, q h ^ d h) =
      (P.coeff d : ℚ) *
        ((∏ h, ((q h).den : ℚ) ^ r h) * ∏ h, q h ^ d h) := by
    rw [algebraMap_int_eq, Int.coe_castRingHom]
    dsimp only
    ring
  rw [hfactor]
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro h _
  simpa only [Int.cast_mul, Int.cast_pow, Int.cast_natCast] using hcoord h

private lemma eval₂_rational_lower_bound_h
  {m : ℕ}
  (P : MvPolynomial (Fin m) ℤ)
  (q : Fin m → ℚ)
  (r : Fin m → ℕ)
  (G : ℕ)
-- given
  (hP : rothDegreeBound P r)
  (hne : MvPolynomial.eval₂ (algebraMap ℤ ℝ) (fun h ↦ (q h : ℝ)) P ≠ 0)
  (hG : (G : ℤ) ∣ rothClearEval P q r) :
-- imply
  (G : ℝ) / (rothDenProduct q r : ℝ) ≤
    |MvPolynomial.eval₂ (algebraMap ℤ ℝ) (fun h ↦ (q h : ℝ)) P| := by
-- proof
  let v : ℚ := MvPolynomial.eval₂ (algebraMap ℤ ℚ) q P
  let D := rothDenProduct q r
  let z := rothClearEval P q r
  have hDpos : 0 < D := by
    dsimp [D, rothDenProduct]
    exact Finset.prod_pos fun h _ ↦ pow_pos (q h).pos _
  have hvCast :
    (v : ℝ) =
        MvPolynomial.eval₂ (algebraMap ℤ ℝ) (fun h ↦ (q h : ℝ)) P := by
    simpa [v] using EvalAlgebraMap.eq.Eval_AlgebraMapFun (P := P) (q := q)
  have hv : v ≠ 0 := by
    intro hz
    apply hne
    rw [← hvCast, hz]
    norm_num
  have heqQ : (D : ℚ) * v = (z : ℚ) := denProduct_mul_eval₂_h P q r hP
  have hz : z ≠ 0 := by
    intro hz0
    rw [hz0, Int.cast_zero] at heqQ
    exact hv ((mul_eq_zero.mp heqQ).resolve_left (by exact_mod_cast (ne_of_gt hDpos)))
  have hGnat : G ≤ z.natAbs := by
    simpa [z] using Int.natAbs_le_of_dvd_ne_zero hG hz
  have hGabs : (G : ℝ) ≤ |(z : ℝ)| := by
    have habs : |(z : ℝ)| = (z.natAbs : ℝ) := by
      rw [← Int.cast_abs]
      norm_num
    rw [habs]
    exact_mod_cast hGnat
  have heqR :
    (D : ℝ) *
        MvPolynomial.eval₂ (algebraMap ℤ ℝ) (fun h ↦ (q h : ℝ)) P =
          (z : ℝ) := by
    rw [← hvCast]
    exact_mod_cast heqQ
  have hmul :
    (G : ℝ) ≤
        (D : ℝ) *
          |MvPolynomial.eval₂ (algebraMap ℤ ℝ) (fun h ↦ (q h : ℝ)) P| := calc
      _ ≤ |(z : ℝ)| := hGabs
      _ = |(D : ℝ) *
          MvPolynomial.eval₂ (algebraMap ℤ ℝ) (fun h ↦ (q h : ℝ)) P| :=
        congrArg abs heqR.symm
      _ = (D : ℝ) *
          |MvPolynomial.eval₂ (algebraMap ℤ ℝ) (fun h ↦ (q h : ℝ)) P| := by
        rw [abs_mul, abs_of_pos (by exact_mod_cast hDpos)]
  rwa [div_le_iff₀ (by exact_mod_cast hDpos), mul_comm]

/--
[roth_ridout_hasse_eq_zero_at_rational_of_taylor_bound](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ}
  (P : MvPolynomial (Fin m) ℤ)
  (x : Fin m → ℝ)
  (q : Fin m → ℚ)
  (r : Fin m → ℕ)
  (T a Q θ s : ℝ)
-- given
  (hr : ∀ h, 0 < r h)
  (hP : rothDegreeBound P r)
  (hvan : rothMvVanishesBelow
    (MvPolynomial.map (algebraMap ℤ ℝ) P) x r T)
  (ha : 0 ≤ a)
  (hQ : 1 < Q)
  (herr : ∀ l : RothMvIndex m,
    ∏ h, |(q h : ℝ) - x h| ^ l h ≤
      Real.rpow Q (-a * rothMvWeight r l))
  (hdiv : ∀ i : RothMvIndex m, rothMvWeight r i ≤ θ →
    ∃ G : ℕ, Real.rpow Q s ≤ G ∧
      (G : ℤ) ∣ rothClearEval (rothMvHasse i P) q r)
  (hmaster : (rothDenProduct q r : ℝ) *
      (((8 ^ (∑ h, r h) * rothMvL1 P : ℕ) : ℝ) *
        ∏ h, max 1 |x h| ^ r h) <
    Real.rpow Q (s + a * (T - θ))) :
-- imply
  ∀ i : RothMvIndex m, rothMvWeight r i ≤ θ →
    MvPolynomial.eval₂ (algebraMap ℤ ℝ) (fun h ↦ (q h : ℝ))
      (rothMvHasse i P) = 0 := by
-- proof
  intro i hi
  by_contra hne
  let Pi := rothMvHasse i P
  let K : ℝ := ((8 ^ (∑ h, r h) * rothMvL1 P : ℕ) : ℝ) *
    ∏ h, max 1 |x h| ^ r h
  let b := a * (T - rothMvWeight r i)
  have hPiDeg : rothDegreeBound Pi r :=
    rothDegreeBoundOver_hasse_h (show rothDegreeBoundOver P r from hP) i
  obtain ⟨G, hGs, hGdvd⟩ := hdiv i hi
  have hlower :=
    eval₂_rational_lower_bound_h Pi q r G hPiDeg hne hGdvd
  have hupper :=
    AbsEval.le.MulMulMulPow8SumRothMvL1Prod_PowMaxRpow.of.All_LeProd_PowAbsSub_RpowMulNegRothMvWeight.Ge_1.Ge_0.RothMvIndex.All_Gt_0
      P x (fun h ↦ (q h : ℝ)) r i T a Q hr hP hvan ha hQ.le herr
  have hDpos : (0 : ℝ) < rothDenProduct q r := by
    exact_mod_cast (show 0 < rothDenProduct q r by
      unfold rothDenProduct
      exact Finset.prod_pos fun h _ ↦ pow_pos (q h).pos _)
  have hGmul :
    (G : ℝ) ≤
        (rothDenProduct q r : ℝ) *
          |MvPolynomial.eval₂ (algebraMap ℤ ℝ) (fun h ↦ (q h : ℝ)) Pi| := calc
      _ =
          (rothDenProduct q r : ℝ) *
            ((G : ℝ) / rothDenProduct q r) := by field_simp
      _ ≤
          (rothDenProduct q r : ℝ) *
            |MvPolynomial.eval₂ (algebraMap ℤ ℝ) (fun h ↦ (q h : ℝ)) Pi| :=
        mul_le_mul_of_nonneg_left hlower hDpos.le
  have hbase :
    Real.rpow Q s ≤
        (rothDenProduct q r : ℝ) *
          |MvPolynomial.eval₂ (algebraMap ℤ ℝ) (fun h ↦ (q h : ℝ)) Pi| :=
    hGs.trans hGmul
  have hb : s + a * (T - θ) ≤ s + b := by
    dsimp [b]
    nlinarith
  have hQpos : 0 < Q := lt_trans (by norm_num) hQ
  have hKb :
    (rothDenProduct q r : ℝ) * K < Real.rpow Q (s + b) :=
    hmaster.trans_le (Real.rpow_le_rpow_of_exponent_le hQ.le hb)
  have hinv :
    Real.rpow Q (s + b) * Real.rpow Q (-b) = Real.rpow Q s := calc
      _ =
          Real.rpow Q ((s + b) + -b) :=
        (Real.rpow_add hQpos (s + b) (-b)).symm
      _ = Real.rpow Q s := by ring_nf
  have hle :
    (rothDenProduct q r : ℝ) *
          |MvPolynomial.eval₂ (algebraMap ℤ ℝ) (fun h ↦ (q h : ℝ)) Pi| ≤
        (rothDenProduct q r : ℝ) * (K * Real.rpow Q (-b)) := by
    gcongr
    simpa [Pi, K, b, mul_assoc] using hupper
  have hsmall :
    (rothDenProduct q r : ℝ) * (K * Real.rpow Q (-b)) <
        Real.rpow Q s := calc
      _ = ((rothDenProduct q r : ℝ) * K) * Real.rpow Q (-b) := by ring
      _ < Real.rpow Q (s + b) * Real.rpow Q (-b) := by
        gcongr
        exact Real.rpow_pos_of_pos hQpos _
      _ = Real.rpow Q s := hinv
  have := not_lt_of_ge (hbase.trans hle) hsmall
  exact this


-- created on 2026-10-21
