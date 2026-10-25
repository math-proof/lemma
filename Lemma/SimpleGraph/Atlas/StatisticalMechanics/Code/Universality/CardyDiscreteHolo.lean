import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.CardyDiscreteHolo.Part6
open StatMech StatMech.Universality StatMech.Universality.CardyLocalConfig


/--
[cardyOmega_cube](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CardyDiscreteHolo.lean)
-/
@[path]
private lemma cardyOmega_cube_eq :
-- imply
  cardyOmega ^ 3 = 1 := by
-- proof
  apply StatMech.Universality.cardyOmega_cube

/--
[cardyOmega_ne_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CardyDiscreteHolo.lean)
-/
@[path]
private lemma cardyOmega_ne_one_eq :
-- imply
  cardyOmega ≠ 1 := by
-- proof
  apply StatMech.Universality.cardyOmega_ne_one

/--
[cardyOmega_sum_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CardyDiscreteHolo.lean)
-/
@[path]
private lemma cardyOmega_sum_zero_eq :
-- imply
  1 + cardyOmega + cardyOmega ^ 2 = 0 := by
-- proof
  apply StatMech.Universality.cardyOmega_sum_zero

/--
[cardyWpow_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CardyDiscreteHolo.lean)
-/
@[path]
private lemma cardyWpow_zero_eq :
-- imply
  cardyWpow 0 = 1 := by
-- proof
  apply StatMech.Universality.cardyWpow_zero

/--
[cardyWpow_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CardyDiscreteHolo.lean)
-/
@[path]
private lemma cardyWpow_one_eq :
-- imply
  cardyWpow 1 = cardyOmega := by
-- proof
  apply StatMech.Universality.cardyWpow_one

/--
[cardyWpow_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CardyDiscreteHolo.lean)
-/
@[path]
private lemma cardyWpow_two_eq :
-- imply
  cardyWpow 2 = cardyOmega ^ 2 := by
-- proof
  apply StatMech.Universality.cardyWpow_two

/--
[cardyWpow_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CardyDiscreteHolo.lean)
-/
@[path]
private lemma cardyWpow_succ_eq
  {k : ZMod 3} :
-- imply
  cardyWpow (k + 1) = cardyOmega * cardyWpow k := by
-- proof
  apply StatMech.Universality.cardyWpow_succ k

/--
[cardyWpow_sum_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CardyDiscreteHolo.lean)
-/
@[path]
private lemma cardyWpow_sum_zero_eq :
-- imply
  cardyWpow 0 + cardyWpow 1 + cardyWpow 2 = 0 := by
-- proof
  apply StatMech.Universality.cardyWpow_sum_zero

/--
[cardyS_eq_combination](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CardyDiscreteHolo.lean)
-/
@[path]
private lemma cardyS_eq_combination_eq
  {L : CardyLocalConfig} :
-- imply
  L.cardyS = L.crossingFun 0 + cardyOmega * L.crossingFun 1 + cardyOmega ^ 2 * L.crossingFun 2 := by
-- proof
  apply StatMech.Universality.CardyLocalConfig.cardyS_eq_combination L

/--
[colorSwap_S_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CardyDiscreteHolo.lean)
-/
@[path]
private lemma colorSwap_S_zero_eq
  {L : CardyLocalConfig} :
-- imply
  L.cardyS = 0 := by
-- proof
  apply StatMech.Universality.CardyLocalConfig.colorSwap_S_zero L

/--
[crossingCombination_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CardyDiscreteHolo.lean)
-/
@[path]
private lemma crossingCombination_zero_eq
  {L : CardyLocalConfig} :
-- imply
  L.crossingFun 0 + cardyOmega * L.crossingFun 1 + cardyOmega ^ 2 * L.crossingFun 2 = 0 := by
-- proof
  apply StatMech.Universality.CardyLocalConfig.crossingCombination_zero L

/--
[triContour_expand](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CardyDiscreteHolo.lean)
-/
@[path]
private lemma triContour_expand_eq
  {F : ℂ → ℂ}
  {z : Fin 3 → ℂ} :
-- imply
  triContour F z = F ((z 0 + z 1) / 2) * (z 1 - z 0) + F ((z 1 + z 2) / 2) * (z 2 - z 1) + F ((z 2 + z 0) / 2) * (z 0 - z 2) := by
-- proof
  apply StatMech.Universality.triContour_expand F z

/--
[triContour_eq_cardyS](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CardyDiscreteHolo.lean)
-/
@[path]
private lemma triContour_eq_cardyS_eq
  {F : ℂ → ℂ}
  {v d : ℂ} :
-- imply
  triContour F (triFace v d) = (cardyOmega - 1) * d * ( F ((triFace v d 0 + triFace v d 1) / 2) + cardyOmega * F ((triFace v d 1 + triFace v d 2) / 2) + cardyOmega ^ 2 * F ((triFace v d 2 + triFace v d 0) / 2) ) := by
-- proof
  apply StatMech.Universality.triContour_eq_cardyS F v d

/--
[cardyDiscrete_CR](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CardyDiscreteHolo.lean)
-/
@[path]
private lemma cardyDiscrete_CR_eq
  {L : CardyLocalConfig}
  {v d : ℂ}
-- given
  (hpq : (triFace v d 0 + triFace v d 1) / 2 ≠ (triFace v d 1 + triFace v d 2) / 2)
  (hpr : (triFace v d 0 + triFace v d 1) / 2 ≠ (triFace v d 2 + triFace v d 0) / 2)
  (hqr : (triFace v d 1 + triFace v d 2) / 2 ≠ (triFace v d 2 + triFace v d 0) / 2) :
-- imply
  triContour (cardyObservable L v d) (triFace v d) = 0 := by
-- proof
  apply StatMech.Universality.cardyDiscrete_CR L v d hpq hpr hqr

/--
[cardyDiscrete_CR_closedPath](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CardyDiscreteHolo.lean)
-/
@[path]
private lemma cardyDiscrete_CR_closedPath_eq
  {L : CardyLocalConfig}
  {faces : Finset ι}
  {tri : ι → ℂ × ℂ}
-- given
  (hdist : ∀ i ∈ faces, (triFace (tri i).1 (tri i).2 0 + triFace (tri i).1 (tri i).2 1) / 2 ≠ (triFace (tri i).1 (tri i).2 1 + triFace (tri i).1 (tri i).2 2) / 2 ∧ (triFace (tri i).1 (tri i).2 0 + triFace (tri i).1 (tri i).2 1) / 2 ≠ (triFace (tri i).1 (tri i).2 2 + triFace (tri i).1 (tri i).2 0) / 2 ∧ (triFace (tri i).1 (tri i).2 1 + triFace (tri i).1 (tri i).2 2) / 2 ≠ (triFace (tri i).1 (tri i).2 2 + triFace (tri i).1 (tri i).2 0) / 2) :
-- imply
  ∑ i ∈ faces, triContour (cardyObservable L (tri i).1 (tri i).2) (triFace (tri i).1 (tri i).2) = 0 := by
-- proof
  apply StatMech.Universality.cardyDiscrete_CR_closedPath L faces tri hdist


-- created on 2026-10-23
