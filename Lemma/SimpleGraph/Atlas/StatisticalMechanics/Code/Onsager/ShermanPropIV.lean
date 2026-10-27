import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.ShermanPropIV.Part2
open StatMech StatMech.Onsager


/--
[ons_neg_one_zpow_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanPropIV.lean)
-/
@[path]
private lemma ons_neg_one_zpow_odd_eq
  {m : ℤ}
-- given
  (h : Odd m) :
-- imply
  (-1 : ℂ) ^ m = -1 := by
-- proof
  apply StatMech.Onsager.ons_neg_one_zpow_odd h

/--
[ons_closed_walk_prod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanPropIV.lean)
-/
@[path]
private lemma ons_closed_walk_prod_eq
  {ω : ℂ}
  {n : ℕ}
  {d : Fin (n + 1) → Fin 4}
-- given
  (hω : ω ≠ 0)
  (hI : ω ^ 2 = Complex.I)
  (hnu : ∀ k : Fin n, d k.succ ≠ d k.castSucc + 2)
  (hclose : d (Fin.last n) = d 0) :
-- imply
  ∃ m : ℤ, (∑ k : Fin n, ons_turnPow (d k.castSucc) (d k.succ)) = 4 * m ∧ ∏ k : Fin n, ons_turnW ω (d k.castSucc) (d k.succ) = (-1) ^ m := by
-- proof
  apply StatMech.Onsager.ons_closed_walk_prod ω hω hI n d hnu hclose

/--
[ons_selfAvoiding_prod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanPropIV.lean)
-/
@[path]
private lemma ons_selfAvoiding_prod_eq
  {ω : ℂ}
  {n : ℕ}
  {d : Fin (n + 1) → Fin 4}
  {m : ℤ}
-- given
  (hω : ω ≠ 0)
  (hI : ω ^ 2 = Complex.I)
  (hnu : ∀ k : Fin n, d k.succ ≠ d k.castSucc + 2)
  (hm : (∑ k : Fin n, ons_turnPow (d k.castSucc) (d k.succ)) = 4 * m)
  (hwind : Odd m) :
-- imply
  ∏ k : Fin n, ons_turnW ω (d k.castSucc) (d k.succ) = -1 := by
-- proof
  apply StatMech.Onsager.ons_selfAvoiding_prod ω hω hI n d hnu m hm hwind

/--
[ons_unitSquare_prod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanPropIV.lean)
-/
@[path]
private lemma ons_unitSquare_prod_eq
  {ω : ℂ}
-- given
  (hω : ω ≠ 0)
  (hI : ω ^ 2 = Complex.I) :
-- imply
  ∏ k : Fin 4, ons_turnW ω ((![0, 1, 2, 3, 0] : Fin 5 → Fin 4) k.castSucc) ((![0, 1, 2, 3, 0] : Fin 5 → Fin 4) k.succ) = -1 := by
-- proof
  apply StatMech.Onsager.ons_unitSquare_prod ω hω hI

/--
[ons_propIV_of_umlaufsatz](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanPropIV.lean)
-/
@[path]
private lemma ons_propIV_of_umlaufsatz_eq
  {ω : ℂ}
  {L n : ℕ}
  {d : Fin (n + 1) → Fin 4}
  {site : Fin (n + 1) → ZMod L × ZMod L}
-- given
  (hU : ons_DiscreteUmlaufsatzKW)
  (hω : ω ≠ 0)
  (hI : ω ^ 2 = Complex.I)
  (hstep : ∀ k : Fin n, site k.succ = ons_dirStep L (d k.castSucc) (site k.castSucc))
  (hnu : ∀ k : Fin n, d k.succ ≠ d k.castSucc + 2)
  (hcd : d (Fin.last n) = d 0)
  (hcs : site (Fin.last n) = site 0)
  (hsa : ons_SelfAvoiding site) :
-- imply
  ∏ k : Fin n, ons_turnW ω (d k.castSucc) (d k.succ) = -1 := by
-- proof
  apply StatMech.Onsager.ons_propIV_of_umlaufsatz hU ω hω hI L n d site hstep hnu hcd hcs hsa


-- created on 2026-10-23
