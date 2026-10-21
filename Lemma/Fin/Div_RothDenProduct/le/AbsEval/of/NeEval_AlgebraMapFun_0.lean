import Mathlib
import Lemma.Fin.MulRothDenProductEvalAlgebraMap.eq.RothClearEval
open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[roth_ridout_eval₂_rational_lower_bound](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ}
  (P : MvPolynomial (Fin m) ℤ)
  (q : Fin m → ℚ)
  (r : Fin m → ℕ)
-- given
  (G : ℕ)
  (hP : rothDegreeBound P r)
  (hne : MvPolynomial.eval₂ (algebraMap ℤ ℝ)
    (fun h ↦ (q h : ℝ)) P ≠ 0)
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
  have hvCast : (v : ℝ) =
    MvPolynomial.eval₂ (algebraMap ℤ ℝ) (fun h ↦ (q h : ℝ)) P := by
    change (algebraMap ℚ ℝ) (MvPolynomial.eval₂ (algebraMap ℤ ℚ) q P) = _
    rw [MvPolynomial.eval₂_comp_left]
    congr 2
  have hv : v ≠ 0 := by
    intro hz
    apply hne
    rw [← hvCast, hz]
    norm_num
  have heqQ : (D : ℚ) * v = (z : ℚ) :=
    MulRothDenProductEvalAlgebraMap.eq.RothClearEval P q r hP
  have hz : z ≠ 0 := by
    intro hz0
    rw [hz0, Int.cast_zero] at heqQ
    exact hv ((mul_eq_zero.mp heqQ).resolve_left
      (by exact_mod_cast (ne_of_gt hDpos) : (D : ℚ) ≠ 0))
  have hGnat : G ≤ z.natAbs := by
    simpa [z] using Int.natAbs_le_of_dvd_ne_zero hG hz
  have hGabs : (G : ℝ) ≤ |(z : ℝ)| := by
    have habs : |(z : ℝ)| = (z.natAbs : ℝ) := by
      rw [← Int.cast_abs]
      norm_num
    rw [habs]
    exact_mod_cast hGnat
  have heqR : (D : ℝ) *
      MvPolynomial.eval₂ (algebraMap ℤ ℝ) (fun h ↦ (q h : ℝ)) P =
        (z : ℝ) := by
    rw [← hvCast]
    exact_mod_cast heqQ
  have hmul : (G : ℝ) ≤ (D : ℝ) *
      |MvPolynomial.eval₂ (algebraMap ℤ ℝ) (fun h ↦ (q h : ℝ)) P| := calc
      _ ≤ |(z : ℝ)| := hGabs
      _ = |(D : ℝ) *
          MvPolynomial.eval₂ (algebraMap ℤ ℝ) (fun h ↦ (q h : ℝ)) P| :=
        congrArg abs heqR.symm
      _ = (D : ℝ) *
          |MvPolynomial.eval₂ (algebraMap ℤ ℝ) (fun h ↦ (q h : ℝ)) P| := by
        rw [abs_mul, abs_of_pos (mod_cast hDpos)]
  have hDposR : (0 : ℝ) < D := by exact_mod_cast hDpos
  rwa [div_le_iff₀ hDposR, mul_comm]


-- created on 2026-10-21
