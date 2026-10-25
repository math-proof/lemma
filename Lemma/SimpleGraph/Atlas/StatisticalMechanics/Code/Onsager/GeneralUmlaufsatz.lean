import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Onsager.GeneralUmlaufsatz
open StatMech StatMech.Onsager StatMech.Onsager.GeneralUmlaufsatz


/--
[zmod2_add_one_add_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/GeneralUmlaufsatz.lean)
-/
@[path]
private lemma zmod2_add_one_add_one_eq
  {n : ℕ}
  [NeZero n]
  {z : ZMod 2} :
-- imply
  z = (z + 1) + 1 := by
-- proof
  apply StatMech.Onsager.GeneralUmlaufsatz.zmod2_add_one_add_one z

/--
[cornerWeight_rightPattern](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/GeneralUmlaufsatz.lean)
-/
@[path]
private lemma cornerWeight_rightPattern_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {vx vy : ℤ}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hn : 3 ≤ n)
  (hNW : rayParity d (vx - 1) vy = rayParity d (vx - 1) (vy - 1) + 1)
  (hSE : rayParity d vx (vy - 1) = rayParity d (vx - 1) (vy - 1) + 1) :
-- imply
  cornerWeight (cornerCount (interiorCells d hclosed) (vx, vy)) = if rayParity d (vx - 1) vy = 1 then (-1 : ℤ) else 1 := by
-- proof
  apply StatMech.Onsager.GeneralUmlaufsatz.cornerWeight_rightPattern d hclosed hsimple hn vx vy hNW hSE

/--
[cornerWeight_rightPattern_NWSE_NE](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/GeneralUmlaufsatz.lean)
-/
@[path]
private lemma cornerWeight_rightPattern_NWSE_NE_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {vx vy : ℤ}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hn : 3 ≤ n)
  (hNW : rayParity d (vx - 1) vy = rayParity d vx vy + 1)
  (hSE : rayParity d vx (vy - 1) = rayParity d vx vy + 1) :
-- imply
  cornerWeight (cornerCount (interiorCells d hclosed) (vx, vy)) = if rayParity d (vx - 1) vy = 1 then (-1 : ℤ) else 1 := by
-- proof
  apply StatMech.Onsager.GeneralUmlaufsatz.cornerWeight_rightPattern_NWSE_NE d hclosed hsimple hn vx vy hNW hSE

/--
[cornerWeight_rightPattern_NESW_NW](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/GeneralUmlaufsatz.lean)
-/
@[path]
private lemma cornerWeight_rightPattern_NESW_NW_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {vx vy : ℤ}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hn : 3 ≤ n)
  (hNE : rayParity d vx vy = rayParity d (vx - 1) vy + 1)
  (hSW : rayParity d (vx - 1) (vy - 1) = rayParity d (vx - 1) vy + 1) :
-- imply
  cornerWeight (cornerCount (interiorCells d hclosed) (vx, vy)) = if rayParity d vx vy = 1 then (-1 : ℤ) else 1 := by
-- proof
  apply StatMech.Onsager.GeneralUmlaufsatz.cornerWeight_rightPattern_NESW_NW d hclosed hsimple hn vx vy hNE hSW

/--
[cornerWeight_rightPattern_NESW_SE](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/GeneralUmlaufsatz.lean)
-/
@[path]
private lemma cornerWeight_rightPattern_NESW_SE_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {vx vy : ℤ}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hn : 3 ≤ n)
  (hNE : rayParity d vx vy = rayParity d vx (vy - 1) + 1)
  (hSW : rayParity d (vx - 1) (vy - 1) = rayParity d vx (vy - 1) + 1) :
-- imply
  cornerWeight (cornerCount (interiorCells d hclosed) (vx, vy)) = if rayParity d vx vy = 1 then (-1 : ℤ) else 1 := by
-- proof
  apply StatMech.Onsager.GeneralUmlaufsatz.cornerWeight_rightPattern_NESW_SE d hclosed hsimple hn vx vy hNE hSW

/--
[rightTurn_ES](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/GeneralUmlaufsatz.lean)
-/
@[path]
private lemma rightTurn_ES_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {i : Fin n}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hn : 3 ≤ n)
  (hei : d i = 0)
  (he : d (i + 1) = 3) :
-- imply
  leftParity d i = leftParity d (i + 1) ∧ cornerWeight (cornerCount (interiorCells d hclosed) (pos d (i + 1))) = -(if leftParity d (i + 1) = 1 then (1 : ℤ) else -1) := by
-- proof
  apply StatMech.Onsager.GeneralUmlaufsatz.rightTurn_ES d hclosed hsimple hn i hei he

/--
[rightTurn_SW](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/GeneralUmlaufsatz.lean)
-/
@[path]
private lemma rightTurn_SW_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {i : Fin n}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hn : 3 ≤ n)
  (hei : d i = 3)
  (he : d (i + 1) = 2) :
-- imply
  leftParity d i = leftParity d (i + 1) ∧ cornerWeight (cornerCount (interiorCells d hclosed) (pos d (i + 1))) = -(if leftParity d (i + 1) = 1 then (1 : ℤ) else -1) := by
-- proof
  apply StatMech.Onsager.GeneralUmlaufsatz.rightTurn_SW d hclosed hsimple hn i hei he

/--
[rightTurn_WN](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/GeneralUmlaufsatz.lean)
-/
@[path]
private lemma rightTurn_WN_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {i : Fin n}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hn : 3 ≤ n)
  (hei : d i = 2)
  (he : d (i + 1) = 1) :
-- imply
  leftParity d i = leftParity d (i + 1) ∧ cornerWeight (cornerCount (interiorCells d hclosed) (pos d (i + 1))) = -(if leftParity d (i + 1) = 1 then (1 : ℤ) else -1) := by
-- proof
  apply StatMech.Onsager.GeneralUmlaufsatz.rightTurn_WN d hclosed hsimple hn i hei he

/--
[rightTurn_NE](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/GeneralUmlaufsatz.lean)
-/
@[path]
private lemma rightTurn_NE_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {i : Fin n}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hn : 3 ≤ n)
  (hei : d i = 1)
  (he : d (i + 1) = 0) :
-- imply
  leftParity d i = leftParity d (i + 1) ∧ cornerWeight (cornerCount (interiorCells d hclosed) (pos d (i + 1))) = -(if leftParity d (i + 1) = 1 then (1 : ℤ) else -1) := by
-- proof
  apply StatMech.Onsager.GeneralUmlaufsatz.rightTurn_NE d hclosed hsimple hn i hei he

/--
[rightTurn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/GeneralUmlaufsatz.lean)
-/
@[path]
private lemma rightTurn_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {i : Fin n}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hn : 3 ≤ n)
  (hr : d (i + 1) - d i = 3) :
-- imply
  leftParity d i = leftParity d (i + 1) ∧ cornerWeight (cornerCount (interiorCells d hclosed) (pos d (i + 1))) = -(if leftParity d (i + 1) = 1 then (1 : ℤ) else -1) := by
-- proof
  apply StatMech.Onsager.GeneralUmlaufsatz.rightTurn d hclosed hsimple hn i hr

/--
[turn_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/GeneralUmlaufsatz.lean)
-/
@[path]
private lemma turn_cases_eq
  {n : ℕ}
  [NeZero n]
  {mu nu : Fin 4}
-- given
  (hnu : nu ≠ mu + 2) :
-- imply
  nu - mu = 0 ∨ nu - mu = 1 ∨ nu - mu = 3 := by
-- proof
  apply StatMech.Onsager.GeneralUmlaufsatz.turn_cases mu nu hnu

/--
[ons_turnPow_eq_of_turn_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/GeneralUmlaufsatz.lean)
-/
@[path]
private lemma ons_turnPow_eq_of_turn_zero_eq
  {n : ℕ}
  [NeZero n]
  {mu nu : Fin 4}
-- given
  (h : nu - mu = 0) :
-- imply
  ons_turnPow mu nu = 0 := by
-- proof
  apply StatMech.Onsager.GeneralUmlaufsatz.ons_turnPow_eq_of_turn_zero h

/--
[ons_turnPow_eq_of_turn_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/GeneralUmlaufsatz.lean)
-/
@[path]
private lemma ons_turnPow_eq_of_turn_one_eq
  {n : ℕ}
  [NeZero n]
  {mu nu : Fin 4}
-- given
  (h : nu - mu = 1) :
-- imply
  ons_turnPow mu nu = 1 := by
-- proof
  apply StatMech.Onsager.GeneralUmlaufsatz.ons_turnPow_eq_of_turn_one h

/--
[ons_turnPow_eq_of_turn_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/GeneralUmlaufsatz.lean)
-/
@[path]
private lemma ons_turnPow_eq_of_turn_three_eq
  {n : ℕ}
  [NeZero n]
  {mu nu : Fin 4}
-- given
  (h : nu - mu = 3) :
-- imply
  ons_turnPow mu nu = -1 := by
-- proof
  apply StatMech.Onsager.GeneralUmlaufsatz.ons_turnPow_eq_of_turn_three h

/--
[leftParity_step_general](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/GeneralUmlaufsatz.lean)
-/
@[path]
private lemma leftParity_step_general_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {i : Fin n}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hn : 3 ≤ n)
  (hnu : ∀ i, d (i + 1) ≠ d i + 2) :
-- imply
  leftParity d i = leftParity d (i + 1) := by
-- proof
  apply StatMech.Onsager.GeneralUmlaufsatz.leftParity_step_general d hclosed hsimple hn hnu i

/--
[leftParity_const_general](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/GeneralUmlaufsatz.lean)
-/
@[path]
private lemma leftParity_const_general_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {k : Fin n}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hn : 3 ≤ n)
  (hnu : ∀ i, d (i + 1) ≠ d i + 2) :
-- imply
  leftParity d k = leftParity d 0 := by
-- proof
  apply StatMech.Onsager.GeneralUmlaufsatz.leftParity_const_general d hclosed hsimple hn hnu k

/--
[cornerWeight_master_general](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/GeneralUmlaufsatz.lean)
-/
@[path]
private lemma cornerWeight_master_general_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {i : Fin n}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hn : 3 ≤ n)
  (hnu : ∀ i, d (i + 1) ≠ d i + 2) :
-- imply
  cornerWeight (cornerCount (interiorCells d hclosed) (pos d (i + 1))) = (if leftParity d 0 = 1 then (1 : ℤ) else -1) * ons_turnPow (d i) (d (i + 1)) := by
-- proof
  apply StatMech.Onsager.GeneralUmlaufsatz.cornerWeight_master_general d hclosed hsimple hn hnu i

/--
[cornerDiff_eq_sign_mul_turnSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/GeneralUmlaufsatz.lean)
-/
@[path]
private lemma cornerDiff_eq_sign_mul_turnSum_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hn : 3 ≤ n)
  (hnu : ∀ i, d (i + 1) ≠ d i + 2) :
-- imply
  cornerDiff (interiorCells d hclosed) = (if leftParity d 0 = 1 then (1 : ℤ) else -1) * ∑ i, ons_turnPow (d i) (d (i + 1)) := by
-- proof
  apply StatMech.Onsager.GeneralUmlaufsatz.cornerDiff_eq_sign_mul_turnSum d hclosed hsimple hn hnu

/--
[turnSum_eq_four_or_neg_four'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/GeneralUmlaufsatz.lean)
-/
@[path]
private lemma turnSum_eq_four_or_neg_four'_eq
  {n : ℕ}
  [NeZero n]
  {m : ℕ}
  {d : Fin (m + 3) → Fin 4}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hnu : ∀ i, d (i + 1) ≠ d i + 2) :
-- imply
  (∑ i, ons_turnPow (d i) (d (i + 1))) = 4 ∨ (∑ i, ons_turnPow (d i) (d (i + 1))) = -4 := by
-- proof
  apply StatMech.Onsager.GeneralUmlaufsatz.turnSum_eq_four_or_neg_four' d hclosed hsimple hnu

/--
[turnSum_eq_four_or_neg_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/GeneralUmlaufsatz.lean)
-/
@[path]
private lemma turnSum_eq_four_or_neg_four_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hn : 3 ≤ n)
  (hnu : ∀ i, d (i + 1) ≠ d i + 2) :
-- imply
  (∑ i, ons_turnPow (d i) (d (i + 1))) = 4 ∨ (∑ i, ons_turnPow (d i) (d (i + 1))) = -4 := by
-- proof
  apply StatMech.Onsager.GeneralUmlaufsatz.turnSum_eq_four_or_neg_four d hclosed hsimple hn hnu

/--
[turnWeightProduct_eq_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/GeneralUmlaufsatz.lean)
-/
@[path]
private lemma turnWeightProduct_eq_neg_one_eq
  {n : ℕ}
  [NeZero n]
  {omega : ℂ}
  {d : Fin n → Fin 4}
-- given
  (homega : omega ≠ 0)
  (hI : omega ^ 2 = Complex.I)
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hn : 3 ≤ n)
  (hnu : ∀ i, d (i + 1) ≠ d i + 2) :
-- imply
  ∏ i, ons_turnW omega (d i) (d (i + 1)) = -1 := by
-- proof
  apply StatMech.Onsager.GeneralUmlaufsatz.turnWeightProduct_eq_neg_one omega homega hI d hclosed hsimple hn hnu


-- created on 2026-10-23
