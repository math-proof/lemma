import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Onsager.WindingParity
open StatMech StatMech.Onsager


/--
[wpar_odd_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WindingParity.lean)
-/
@[path]
private lemma wpar_odd_ne_zero_eq
  {m : ℤ}
-- given
  (h : Odd m) :
-- imply
  m ≠ 0 := by
-- proof
  apply StatMech.Onsager.wpar_odd_ne_zero h

/--
[wpar_oddWinding_forces_winds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WindingParity.lean)
-/
@[path]
private lemma wpar_oddWinding_forces_winds_eq
  {n : ℕ}
  {d : Fin (n + 1) → Fin 4}
  {m : ℤ}
-- given
  (hm : (∑ k : Fin n, ons_turnPow (d k.castSucc) (d k.succ)) = 4 * m)
  (hodd : Odd m) :
-- imply
  (∑ k : Fin n, ons_turnPow (d k.castSucc) (d k.succ)) ≠ 0 := by
-- proof
  apply StatMech.Onsager.wpar_oddWinding_forces_winds n d m hm hodd

/--
[wpar_straight_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WindingParity.lean)
-/
@[path]
private lemma wpar_straight_step_eq :
-- imply
  ∀ k : Fin 2, wpar_siteStraight k.succ = ons_dirStep 2 (wpar_dStraight k.castSucc) (wpar_siteStraight k.castSucc) := by
-- proof
  apply StatMech.Onsager.wpar_straight_step

/--
[wpar_straight_nu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WindingParity.lean)
-/
@[path]
private lemma wpar_straight_nu_eq :
-- imply
  ∀ k : Fin 2, wpar_dStraight k.succ ≠ wpar_dStraight k.castSucc + 2 := by
-- proof
  apply StatMech.Onsager.wpar_straight_nu

/--
[wpar_straight_closeDir](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WindingParity.lean)
-/
@[path]
private lemma wpar_straight_closeDir_eq :
-- imply
  wpar_dStraight (Fin.last 2) = wpar_dStraight 0 := by
-- proof
  apply StatMech.Onsager.wpar_straight_closeDir

/--
[wpar_straight_closeSite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WindingParity.lean)
-/
@[path]
private lemma wpar_straight_closeSite_eq :
-- imply
  wpar_siteStraight (Fin.last 2) = wpar_siteStraight 0 := by
-- proof
  apply StatMech.Onsager.wpar_straight_closeSite

/--
[wpar_straight_selfAvoiding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WindingParity.lean)
-/
@[path]
private lemma wpar_straight_selfAvoiding_eq :
-- imply
  ons_SelfAvoiding wpar_siteStraight := by
-- proof
  apply StatMech.Onsager.wpar_straight_selfAvoiding

/--
[wpar_straight_turnSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WindingParity.lean)
-/
@[path]
private lemma wpar_straight_turnSum_eq :
-- imply
  (∑ k : Fin 2, ons_turnPow (wpar_dStraight k.castSucc) (wpar_dStraight k.succ)) = 4 * 0 := by
-- proof
  apply StatMech.Onsager.wpar_straight_turnSum

/--
[wpar_umlaufsatzKW_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WindingParity.lean)
-/
@[path]
private lemma wpar_umlaufsatzKW_false_eq :
-- imply
  ¬ ons_DiscreteUmlaufsatzKW := by
-- proof
  apply StatMech.Onsager.wpar_umlaufsatzKW_false


-- created on 2026-10-23
