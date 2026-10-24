import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Onsager.GroundUpWinding
open StatMech StatMech.Onsager StatMech.Onsager.GroundUp


/--
[rect_angleSum_iff_balance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/GroundUpWinding.lean)
-/
@[path]
private lemma rect_angleSum_iff_balance_eq
  {c r : ℤ} :
-- imply
  (90 * c + 270 * r = 180 * (c + r) - 360) ↔ (c - r = 4) := by
-- proof
  apply StatMech.Onsager.GroundUp.rect_angleSum_iff_balance c r

/--
[balance_form](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/GroundUpWinding.lean)
-/
@[path]
private lemma balance_form_eq
  {c r : ℤ} :
-- imply
  (c - r = 4 ↔ 90 * (c - r) = 360) ∧ (c - r = -4 ↔ 90 * (c - r) = -360) := by
-- proof
  apply StatMech.Onsager.GroundUp.balance_form c r

/--
[turnSum_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/GroundUpWinding.lean)
-/
@[path]
private lemma turnSum_eq_eq
  {n : ℕ}
  {t : Fin n → ℤ}
-- given
  (h : ∀ i, t i = 1 ∨ t i = -1) :
-- imply
  turnSum t = (convexCount t : ℤ) - reflexCount t := by
-- proof
  apply StatMech.Onsager.GroundUp.turnSum_eq t h

/--
[card_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/GroundUpWinding.lean)
-/
@[path]
private lemma card_split_eq
  {n : ℕ}
  {t : Fin n → ℤ}
-- given
  (h : ∀ i, t i = 1 ∨ t i = -1) :
-- imply
  convexCount t + reflexCount t = n := by
-- proof
  apply StatMech.Onsager.GroundUp.card_split t h

/--
[balance_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/GroundUpWinding.lean)
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
  apply StatMech.Onsager.GroundUp.balance_split c r c₁ r₁ c₂ r₂ hc hr

/--
[balance_of_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/GroundUpWinding.lean)
-/
@[path]
private lemma balance_of_split_eq
  {c r c₁ r₁ c₂ r₂ : ℤ}
-- given
  (hc : c₁ + c₂ = c + 3)
  (hr : r₁ + r₂ = r - 1)
  (h₁ : c₁ - r₁ = 4)
  (h₂ : c₂ - r₂ = 4) :
-- imply
  c - r = 4 := by
-- proof
  apply StatMech.Onsager.GroundUp.balance_of_split c r c₁ r₁ c₂ r₂ hc hr h₁ h₂

/--
[RectPolygonData.umlaufsatz_aux](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/GroundUpWinding.lean)
-/
@[path]
private lemma umlaufsatz_aux_eq
  {D : RectPolygonData} :
-- imply
  ∀ n : ℕ, ∀ P : D.Poly, D.size P = n → D.simple P → D.balance P = 4 := by
-- proof
  apply StatMech.Onsager.GroundUp.RectPolygonData.umlaufsatz_aux D

/--
[RectPolygonData.umlaufsatz](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/GroundUpWinding.lean)
-/
@[path]
private lemma umlaufsatz_eq
  {D : RectPolygonData}
  {P : D.Poly}
-- given
  (hP : D.simple P) :
-- imply
  D.balance P = 4 := by
-- proof
  apply StatMech.Onsager.GroundUp.RectPolygonData.umlaufsatz D P hP

/--
[staircase_balance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/GroundUpWinding.lean)
-/
@[path]
private lemma staircase_balance_eq
  {k : ℕ} :
-- imply
  staircaseModel.balance k = 4 := by
-- proof
  apply StatMech.Onsager.GroundUp.staircase_balance k


-- created on 2026-10-23
