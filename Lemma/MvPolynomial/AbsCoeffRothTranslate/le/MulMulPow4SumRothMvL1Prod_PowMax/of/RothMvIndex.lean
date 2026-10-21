import Mathlib
import Lemma.MvPolynomial.RothHelpers
open MathlibExt.NumberTheory.RothAuxiliary
open MvPolynomial


/--
[roth_abs_translate_hasse_coeff_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ}
  (P : MvPolynomial (Fin m) ℤ) (x : Fin m → ℝ) (r : Fin m → ℕ)
  (hP : rothDegreeBound P r) (i l : RothMvIndex m) :
-- imply
  |(rothTranslate m x
      (rothMvHasse i (MvPolynomial.map (algebraMap ℤ ℝ) P))).coeff l| ≤
    ((4 ^ (∑ h, r h) * rothMvL1 P : ℕ) : ℝ) *
      ∏ h, max 1 |x h| ^ r h := by
-- proof
  let Pi := rothMvHasse i P
  let Pil := rothMvHasse l Pi
  have hPiDeg : rothDegreeBound Pi r :=
    rothDegreeBoundOver_hasse_h (show rothDegreeBoundOver P r from hP) i
  have hPilDeg : rothDegreeBound Pil r :=
    rothDegreeBoundOver_hasse_h (show rothDegreeBoundOver Pi r from hPiDeg) l
  have hPiL1 : rothMvL1 Pi ≤ 2 ^ (∑ h, r h) * rothMvL1 P :=
    rothMvL1_hasse_le_h P i r hP
  have hPilL1 : rothMvL1 Pil ≤ 4 ^ (∑ h, r h) * rothMvL1 P := calc
    _ ≤ 2 ^ (∑ h, r h) * rothMvL1 Pi :=
      rothMvL1_hasse_le_h Pi l r hPiDeg
    _ ≤ 2 ^ (∑ h, r h) * (2 ^ (∑ h, r h) * rothMvL1 P) := by
      gcongr
    _ = 4 ^ (∑ h, r h) * rothMvL1 P := by
      rw [← mul_assoc, ← mul_pow]
      norm_num
  rw [rothTranslate_coeff_eq_eval_hasse_h]
  have hmap :
    rothMvHasse l
      (rothMvHasse i (MvPolynomial.map (algebraMap ℤ ℝ) P)) =
      MvPolynomial.map (algebraMap ℤ ℝ) Pil := by
    dsimp [Pil, Pi]
    rw [← rothMvHasse_map_h, ← rothMvHasse_map_h]
  rw [hmap, ← MvPolynomial.eval₂_eq_eval_map]
  calc
    _ ≤ (rothMvL1 Pil : ℝ) * ∏ h, max 1 |x h| ^ r h :=
      roth_abs_eval₂_le_l1_h Pil x r hPilDeg
    _ ≤ ((4 ^ (∑ h, r h) * rothMvL1 P : ℕ) : ℝ) *
        ∏ h, max 1 |x h| ^ r h := by
      gcongr


-- created on 2026-10-21
