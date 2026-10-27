import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.PolygonWalk.Part3
open StatMech StatMech.Onsager StatMech.Onsager.PolygonWalk


/--
[cross_unit_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PolygonWalk.lean)
-/
@[path]
private lemma cross_unit_mem_eq
  {a b : Pt}
-- given
  (ha : isUnitDir a)
  (hb : isUnitDir b) :
-- imply
  cross a b = -1 ∨ cross a b = 0 ∨ cross a b = 1 := by
-- proof
  apply StatMech.Onsager.PolygonWalk.cross_unit_mem a b ha hb

/--
[cross_swap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PolygonWalk.lean)
-/
@[path]
private lemma cross_swap_eq
  {a b : Pt} :
-- imply
  cross b a = - cross a b := by
-- proof
  apply StatMech.Onsager.PolygonWalk.cross_swap a b

/--
[cross_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PolygonWalk.lean)
-/
@[path]
private lemma cross_self_eq
  {a : Pt} :
-- imply
  cross a a = 0 := by
-- proof
  apply StatMech.Onsager.PolygonWalk.cross_self a

/--
[balance_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PolygonWalk.lean)
-/
@[path]
private lemma balance_split_eq
  {c r c₁ r₁ c₂ r₂ : ℤ}
-- given
  (hc : c₁ + c₂ = c + 3)
  (hr : r₁ + r₂ = r - 1) :
-- imply
  (c - r) = (c₁ - r₁) + (c₂ - r₂) - 4 := by
-- proof
  apply StatMech.Onsager.PolygonWalk.balance_split c r c₁ r₁ c₂ r₂ hc hr

/--
[cornerBalance_eq_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PolygonWalk.lean)
-/
@[path]
private lemma cornerBalance_eq_count_eq
  {n : ℕ}
  {t : Fin n → ℤ}
  [DecidablePred fun i => t i = 1]
  [DecidablePred fun i => t i = -1]
-- given
  (h : ∀ i, t i = -1 ∨ t i = 0 ∨ t i = 1) :
-- imply
  cornerBalance t = ((Finset.univ.filter fun i => t i = 1).card : ℤ) - ((Finset.univ.filter fun i => t i = -1).card : ℤ) := by
-- proof
  apply StatMech.Onsager.PolygonWalk.cornerBalance_eq_count t h

/--
[cross_congr_dirCode](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PolygonWalk.lean)
-/
@[path]
private lemma cross_congr_dirCode_eq
  {a b : Pt}
-- given
  (ha : isUnitDir a)
  (hb : isUnitDir b)
  (hnu : b ≠ (-a.1, -a.2)) :
-- imply
  ((cross a b : ℤ) : ZMod 4) = dirCode b - dirCode a := by
-- proof
  apply StatMech.Onsager.PolygonWalk.cross_congr_dirCode a b ha hb hnu

/--
[cornerBalance_mod4](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PolygonWalk.lean)
-/
@[path]
private lemma cornerBalance_mod4_eq
  {n : ℕ}
  [NeZero n]
  {dir : Fin n → Pt}
-- given
  (hunit : ∀ i, isUnitDir (dir i))
  (hnu : ∀ i, dir (i + 1) ≠ (-(dir i).1, -(dir i).2)) :
-- imply
  ((cornerBalance (fun i => cross (dir i) (dir (i + 1))) : ℤ) : ZMod 4) = 0 := by
-- proof
  apply StatMech.Onsager.PolygonWalk.cornerBalance_mod4 dir hunit hnu


-- created on 2026-10-23
