import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPreferenceInterface.Part14
open Set SimpleGraph StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[reachable_of_only_two_odd_degree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean)
-/
@[path]
private lemma reachable_of_only_two_odd_degree_eq
  [Fintype W]
  {G : SimpleGraph W}
  [DecidableRel G.Adj]
  {l r : W}
-- given
  (hl : Odd (G.degree l))
  (hodd : ∀ v, Odd (G.degree v) → v = l ∨ v = r) :
-- imply
  G.Reachable l r := by
-- proof
  apply StatMech.FK.PeriodicPlanar.reachable_of_only_two_odd_degree G l r hl hodd

/--
[boolTransitionCount_parity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean)
-/
@[path]
private lemma boolTransitionCount_parity_eq
  {a : Bool}
  {xs : List Bool} :
-- imply
  boolTransitionCount (a :: xs) % 2 = if a = (a :: xs).getLastD a then 0 else 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.boolTransitionCount_parity a xs

/--
[boolTransitionCount_odd_of_ne_last](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean)
-/
@[path]
private lemma boolTransitionCount_odd_of_ne_last_eq
  {a : Bool}
  {xs : List Bool}
-- given
  (hne : a ≠ (a :: xs).getLastD a) :
-- imply
  Odd (boolTransitionCount (a :: xs)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.boolTransitionCount_odd_of_ne_last a xs hne

/--
[finBoolTransitionCount_parity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean)
-/
@[path]
private lemma finBoolTransitionCount_parity_eq
  {n : Nat}
  {f : Fin (n + 1) → Bool} :
-- imply
  finBoolTransitionCount f % 2 = if f 0 = f (Fin.last n) then 0 else 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.finBoolTransitionCount_parity f

/--
[finBoolTransitionCount_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean)
-/
@[path]
private lemma finBoolTransitionCount_odd_eq
  {n : Nat}
  {f : Fin (n + 1) → Bool}
-- given
  (hne : f 0 ≠ f (Fin.last n)) :
-- imply
  Odd (finBoolTransitionCount f) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.finBoolTransitionCount_odd f hne

/--
[boolTriangleTransitionCount_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean)
-/
@[path]
private lemma boolTriangleTransitionCount_even_eq
  {a b c : Bool} :
-- imply
  Even (boolTriangleTransitionCount a b c) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.boolTriangleTransitionCount_even a b c

/--
[preferenceTriangleOther_ne_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean)
-/
@[path]
private lemma preferenceTriangleOther_ne_self_eq
  {n m : Nat}
  {t : PreferenceTriangle n m}
  {k : Fin 3} :
-- imply
  preferenceTriangleOther t k ≠ .triangle t := by
-- proof
  apply StatMech.FK.PeriodicPlanar.preferenceTriangleOther_ne_self t k

/--
[preferenceTriangleOther_zero_ne_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean)
-/
@[path]
private lemma preferenceTriangleOther_zero_ne_one_eq
  {n m : Nat}
  {t : PreferenceTriangle n m} :
-- imply
  preferenceTriangleOther t 0 ≠ preferenceTriangleOther t 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.preferenceTriangleOther_zero_ne_one t

/--
[preferenceTriangleOther_zero_ne_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean)
-/
@[path]
private lemma preferenceTriangleOther_zero_ne_two_eq
  {n m : Nat}
  {t : PreferenceTriangle n m} :
-- imply
  preferenceTriangleOther t 0 ≠ preferenceTriangleOther t 2 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.preferenceTriangleOther_zero_ne_two t

/--
[preferenceTriangleOther_one_ne_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean)
-/
@[path]
private lemma preferenceTriangleOther_one_ne_two_eq
  {n m : Nat}
  {t : PreferenceTriangle n m} :
-- imply
  preferenceTriangleOther t 1 ≠ preferenceTriangleOther t 2 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.preferenceTriangleOther_one_ne_two t

/--
[preferenceTriangleOther_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean)
-/
@[path]
private lemma preferenceTriangleOther_injective_eq
  {n m : Nat}
  {t : PreferenceTriangle n m} :
-- imply
  Function.Injective (preferenceTriangleOther t) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.preferenceTriangleOther_injective t

/--
[preferenceTriangleOther_reciprocal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean)
-/
@[path]
private lemma preferenceTriangleOther_reciprocal_eq
  {n m : Nat}
  {color : PreferenceGridVertex n m → Bool}
  {t s : PreferenceTriangle n m}
  {k : Fin 3}
-- given
  (h : preferenceTriangleOther t k = .triangle s) :
-- imply
  ∃ l : Fin 3, preferenceTriangleOther s l = .triangle t ∧ (preferenceTriangleSideActive color s l ↔ preferenceTriangleSideActive color t k) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.preferenceTriangleOther_reciprocal color t s k h

/--
[preferenceInterfaceAdj_triangle_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean)
-/
@[path]
private lemma preferenceInterfaceAdj_triangle_iff_eq
  {n m : Nat}
  {color : PreferenceGridVertex n m → Bool}
  {t : PreferenceTriangle n m}
  {v : PreferenceInterfaceNode n m} :
-- imply
  preferenceInterfaceAdj color (.triangle t) v ↔ ∃ k : Fin 3, preferenceTriangleSideActive color t k ∧ v = preferenceTriangleOther t k := by
-- proof
  apply StatMech.FK.PeriodicPlanar.preferenceInterfaceAdj_triangle_iff color t v

/--
[preferenceInterface_neighborFinset_triangle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean)
-/
@[path]
private lemma preferenceInterface_neighborFinset_triangle_eq
  {n m : Nat}
  {color : PreferenceGridVertex n m → Bool}
  {t : PreferenceTriangle n m} :
-- imply
  (preferenceInterfaceGraph color).neighborFinset (.triangle t) = (preferenceActiveSides color t).image (preferenceTriangleOther t) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.preferenceInterface_neighborFinset_triangle color t

/--
[preferenceInterface_degree_triangle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean)
-/
@[path]
private lemma preferenceInterface_degree_triangle_eq
  {n m : Nat}
  {color : PreferenceGridVertex n m → Bool}
  {t : PreferenceTriangle n m} :
-- imply
  (preferenceInterfaceGraph color).degree (.triangle t) = (preferenceActiveSides color t).card := by
-- proof
  apply StatMech.FK.PeriodicPlanar.preferenceInterface_degree_triangle color t

/--
[preferenceActiveSides_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean)
-/
@[path]
private lemma preferenceActiveSides_card_eq
  {n m : Nat}
  {color : PreferenceGridVertex n m → Bool}
  {t : PreferenceTriangle n m} :
-- imply
  (preferenceActiveSides color t).card = boolTriangleTransitionCount (color (preferenceTriangleVertex t 0)) (color (preferenceTriangleVertex t 1)) (color (preferenceTriangleVertex t 2)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.preferenceActiveSides_card color t

/--
[preferenceInterface_triangle_even_degree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean)
-/
@[path]
private lemma preferenceInterface_triangle_even_degree_eq
  {n m : Nat}
  {color : PreferenceGridVertex n m → Bool}
  {t : PreferenceTriangle n m} :
-- imply
  Even ((preferenceInterfaceGraph color).degree (.triangle t)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.preferenceInterface_triangle_even_degree color t

/--
[preferenceTriangleOther_eq_left_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean)
-/
@[path]
private lemma preferenceTriangleOther_eq_left_iff_eq
  {n m : Nat}
  {t : PreferenceTriangle n m}
  {k : Fin 3} :
-- imply
  preferenceTriangleOther t k = .left ↔ t.upper = true ∧ t.col.val = 0 ∧ k = 2 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.preferenceTriangleOther_eq_left_iff t k

/--
[preferenceTriangleOther_eq_right_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean)
-/
@[path]
private lemma preferenceTriangleOther_eq_right_iff_eq
  {n m : Nat}
  {t : PreferenceTriangle n m}
  {k : Fin 3} :
-- imply
  preferenceTriangleOther t k = .right ↔ t.upper = false ∧ t.col.val + 1 = n ∧ k = 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.preferenceTriangleOther_eq_right_iff t k

/--
[preferenceTriangleOther_eq_bottom_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean)
-/
@[path]
private lemma preferenceTriangleOther_eq_bottom_iff_eq
  {n m : Nat}
  {t : PreferenceTriangle n m}
  {k : Fin 3} :
-- imply
  preferenceTriangleOther t k = .bottom ↔ t.upper = false ∧ t.row.val = 0 ∧ k = 0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.preferenceTriangleOther_eq_bottom_iff t k

/--
[preferenceTriangleOther_eq_top_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean)
-/
@[path]
private lemma preferenceTriangleOther_eq_top_iff_eq
  {n m : Nat}
  {t : PreferenceTriangle n m}
  {k : Fin 3} :
-- imply
  preferenceTriangleOther t k = .top ↔ t.upper = true ∧ t.row.val + 1 = m ∧ k = 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.preferenceTriangleOther_eq_top_iff t k

/--
[preferenceInterfaceAdj_exterior_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean)
-/
@[path]
private lemma preferenceInterfaceAdj_exterior_iff_eq
  {n m : Nat}
  {color : PreferenceGridVertex n m → Bool}
  {side : PreferenceInterfaceNode n m}
  {v : PreferenceInterfaceNode n m}
-- given
  (hside : ∀ t : PreferenceTriangle n m, side ≠ .triangle t) :
-- imply
  preferenceInterfaceAdj color side v ↔ ∃ (t : PreferenceTriangle n m) (k : Fin 3), preferenceTriangleSideActive color t k ∧ preferenceTriangleOther t k = side ∧ v = .triangle t := by
-- proof
  apply StatMech.FK.PeriodicPlanar.preferenceInterfaceAdj_exterior_iff color side hside v

/--
[preferenceInterface_neighborFinset_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean)
-/
@[path]
private lemma preferenceInterface_neighborFinset_left_eq
  {n m : Nat}
  {color : PreferenceGridVertex n m → Bool}
-- given
  (hn : 0 < n) :
-- imply
  (preferenceInterfaceGraph color).neighborFinset (.left) = (preferenceLeftActiveRows color hn).image fun j => .triangle (preferenceLeftTriangle hn j) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.preferenceInterface_neighborFinset_left color hn

/--
[preferenceInterface_degree_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean)
-/
@[path]
private lemma preferenceInterface_degree_left_eq
  {n m : Nat}
  {color : PreferenceGridVertex n m → Bool}
-- given
  (hn : 0 < n) :
-- imply
  (preferenceInterfaceGraph color).degree (.left) = (preferenceLeftActiveRows (n := n) (m := m) color hn).card := by
-- proof
  apply StatMech.FK.PeriodicPlanar.preferenceInterface_degree_left color hn

/--
[preferenceLeftActiveRows_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean)
-/
@[path]
private lemma preferenceLeftActiveRows_card_eq
  {n m : Nat}
  {color : PreferenceGridVertex n m → Bool}
-- given
  (hn : 0 < n) :
-- imply
  (preferenceLeftActiveRows (n := n) (m := m) color hn).card = finBoolTransitionCount (preferenceLeftColor (n := n) (m := m) color) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.preferenceLeftActiveRows_card color hn

/--
[preferenceInterface_left_odd_degree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean)
-/
@[path]
private lemma preferenceInterface_left_odd_degree_eq
  {n m : Nat}
  {color : PreferenceGridVertex n m → Bool}
-- given
  (hn : 0 < n)
  (hend : preferenceLeftColor (n := n) (m := m) color 0 ≠ preferenceLeftColor (n := n) (m := m) color (Fin.last m)) :
-- imply
  Odd ((preferenceInterfaceGraph color).degree (.left)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.preferenceInterface_left_odd_degree color hn hend

/--
[preferenceInterface_exterior_degree_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean)
-/
@[path]
private lemma preferenceInterface_exterior_degree_zero_eq
  {n m : Nat}
  {color : PreferenceGridVertex n m → Bool}
  {side : PreferenceInterfaceNode n m}
-- given
  (hside : ∀ t : PreferenceTriangle n m, side ≠ .triangle t)
  (hinactive : ∀ (t : PreferenceTriangle n m) (k : Fin 3), preferenceTriangleOther t k = side → ¬preferenceTriangleSideActive color t k) :
-- imply
  (preferenceInterfaceGraph color).degree side = 0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.preferenceInterface_exterior_degree_zero color side hside hinactive

/--
[preferenceInterface_bottom_degree_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean)
-/
@[path]
private lemma preferenceInterface_bottom_degree_zero_eq
  {n m : Nat}
  {color : PreferenceGridVertex n m → Bool}
  {b : Bool}
-- given
  (hbottom : ∀ i : Fin (n + 1), color (i, 0) = b) :
-- imply
  (preferenceInterfaceGraph color).degree (.bottom) = 0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.preferenceInterface_bottom_degree_zero color b hbottom

/--
[preferenceInterface_top_degree_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean)
-/
@[path]
private lemma preferenceInterface_top_degree_zero_eq
  {n m : Nat}
  {color : PreferenceGridVertex n m → Bool}
  {b : Bool}
-- given
  (htop : ∀ i : Fin (n + 1), color (i, Fin.last m) = b) :
-- imply
  (preferenceInterfaceGraph color).degree (.top) = 0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.preferenceInterface_top_degree_zero color b htop

/--
[preferenceInterface_left_reachable_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean)
-/
@[path]
private lemma preferenceInterface_left_reachable_right_eq
  {n m : Nat}
  {color : PreferenceGridVertex n m → Bool}
  {bottomColor topColor : Bool}
-- given
  (hn : 0 < n)
  (hbottom : ∀ i : Fin (n + 1), color (i, 0) = bottomColor)
  (htop : ∀ i : Fin (n + 1), color (i, Fin.last m) = topColor)
  (hne : bottomColor ≠ topColor) :
-- imply
  (preferenceInterfaceGraph color).Reachable (.left) (.right) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.preferenceInterface_left_reachable_right color hn bottomColor topColor hbottom htop hne

/--
[preferenceRightFlagChain_of_path](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean)
-/
@[path]
private lemma preferenceRightFlagChain_of_path_eq
  {n m : Nat}
  {color : PreferenceGridVertex n m → Bool}
-- given
  (hbottom : (preferenceInterfaceGraph color).degree (.bottom) = 0)
  (htop : (preferenceInterfaceGraph color).degree (.top) = 0) :
-- imply
  ∀ {u z : PreferenceInterfaceNode n m} (p : (preferenceInterfaceGraph color).Walk u z), z = .right → p.IsPath → .left ∉ p.support → ∀ t : PreferenceTriangle n m, u = .triangle t → PreferenceRightFlagChain color t := by
-- proof
  apply StatMech.FK.PeriodicPlanar.preferenceRightFlagChain_of_path color hbottom htop

/--
[preferenceFlagCrossing_of_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean)
-/
@[path]
private lemma preferenceFlagCrossing_of_reachable_eq
  {n m : Nat}
  {color : PreferenceGridVertex n m → Bool}
-- given
  (hbottom : (preferenceInterfaceGraph color).degree (.bottom) = 0)
  (htop : (preferenceInterfaceGraph color).degree (.top) = 0)
  (hreach : (preferenceInterfaceGraph color).Reachable (.left) (.right)) :
-- imply
  PreferenceFlagCrossing color := by
-- proof
  apply StatMech.FK.PeriodicPlanar.preferenceFlagCrossing_of_reachable color hbottom htop hreach

/--
[preferenceTriangleSideTrueFalse_color](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean)
-/
@[path]
private lemma preferenceTriangleSideTrueFalse_color_eq
  {n m : Nat}
  {color : PreferenceGridVertex n m → Bool}
  {t : PreferenceTriangle n m}
  {k : Fin 3}
-- given
  (hactive : preferenceTriangleSideActive color t k) :
-- imply
  color (preferenceTriangleSideTrue color t k) = true ∧ color (preferenceTriangleSideFalse color t k) = false := by
-- proof
  apply StatMech.FK.PeriodicPlanar.preferenceTriangleSideTrueFalse_color color t k hactive

/--
[preferenceTriangleSide_king](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean)
-/
@[path]
private lemma preferenceTriangleSide_king_eq
  {n m : Nat}
  {t : PreferenceTriangle n m}
  {k : Fin 3} :
-- imply
  KingAdj (preferenceGridSite (preferenceTriangleVertex t k)) (preferenceGridSite (preferenceTriangleVertex t (preferenceTriangleNext k))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.preferenceTriangleSide_king t k

/--
[preferenceTriangleSideTrueFalse_king](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean)
-/
@[path]
private lemma preferenceTriangleSideTrueFalse_king_eq
  {n m : Nat}
  {color : PreferenceGridVertex n m → Bool}
  {t : PreferenceTriangle n m}
  {k : Fin 3} :
-- imply
  KingAdj (preferenceGridSite (preferenceTriangleSideTrue color t k)) (preferenceGridSite (preferenceTriangleSideFalse color t k)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.preferenceTriangleSideTrueFalse_king color t k

/--
[preferenceTriangleVertex_king_or_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean)
-/
@[path]
private lemma preferenceTriangleVertex_king_or_eq_eq
  {n m : Nat}
  {t : PreferenceTriangle n m}
  {k l : Fin 3} :
-- imply
  preferenceTriangleVertex t k = preferenceTriangleVertex t l ∨ KingAdj (preferenceGridSite (preferenceTriangleVertex t k)) (preferenceGridSite (preferenceTriangleVertex t l)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.preferenceTriangleVertex_king_or_eq t k l

/--
[preferenceTriangleSideTrue_king_or_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean)
-/
@[path]
private lemma preferenceTriangleSideTrue_king_or_eq_eq
  {n m : Nat}
  {color : PreferenceGridVertex n m → Bool}
  {t : PreferenceTriangle n m}
  {k l : Fin 3} :
-- imply
  preferenceTriangleSideTrue color t k = preferenceTriangleSideTrue color t l ∨ KingAdj (preferenceGridSite (preferenceTriangleSideTrue color t k)) (preferenceGridSite (preferenceTriangleSideTrue color t l)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.preferenceTriangleSideTrue_king_or_eq color t k l

/--
[preferenceTriangleOther_reciprocal_vertices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean)
-/
@[path]
private lemma preferenceTriangleOther_reciprocal_vertices_eq
  {n m : Nat}
  {t s : PreferenceTriangle n m}
  {k : Fin 3}
-- given
  (hforward : preferenceTriangleOther t k = .triangle s) :
-- imply
  ∃ l : Fin 3, preferenceTriangleOther s l = .triangle t ∧ preferenceTriangleVertex s l = preferenceTriangleVertex t (preferenceTriangleNext k) ∧ preferenceTriangleVertex s (preferenceTriangleNext l) = preferenceTriangleVertex t k := by
-- proof
  apply StatMech.FK.PeriodicPlanar.preferenceTriangleOther_reciprocal_vertices t s k hforward

/--
[preferenceTriangleSideTrue_swap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean)
-/
@[path]
private lemma preferenceTriangleSideTrue_swap_eq
  {n m : Nat}
  {color : PreferenceGridVertex n m → Bool}
  {a b : PreferenceGridVertex n m}
-- given
  (h : color a ≠ color b) :
-- imply
  (if color a = true then a else b) = (if color b = true then b else a) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.preferenceTriangleSideTrue_swap color a b h

/--
[preferenceTriangleSideTrue_reciprocal_exists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean)
-/
@[path]
private lemma preferenceTriangleSideTrue_reciprocal_exists_eq
  {n m : Nat}
  {color : PreferenceGridVertex n m → Bool}
  {t s : PreferenceTriangle n m}
  {k : Fin 3}
-- given
  (hforward : preferenceTriangleOther t k = .triangle s)
  (hactive : preferenceTriangleSideActive color t k) :
-- imply
  ∃ l : Fin 3, preferenceTriangleOther s l = .triangle t ∧ preferenceTriangleSideActive color s l ∧ preferenceTriangleSideTrue color t k = preferenceTriangleSideTrue color s l := by
-- proof
  apply StatMech.FK.PeriodicPlanar.preferenceTriangleSideTrue_reciprocal_exists color t s k hforward hactive

/--
[preferenceSideBoundaryPoint_reachable_sameTriangle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean)
-/
@[path]
private lemma preferenceSideBoundaryPoint_reachable_sameTriangle_eq
  {n m : Nat}
  {color : PreferenceGridVertex n m → Bool}
  {t : PreferenceTriangle n m}
  {k l : Fin 3}
-- given
  (hk : preferenceTriangleSideActive color t k)
  (hl : preferenceTriangleSideActive color t l) :
-- imply
  (preferenceGridBoundaryGraph color).Reachable (preferenceSideBoundaryPoint color t k hk) (preferenceSideBoundaryPoint color t l hl) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.preferenceSideBoundaryPoint_reachable_sameTriangle color t k l hk hl

/--
[PreferenceRightFlagChain.boundaryReachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean)
-/
@[path]
private lemma boundaryReachable_eq
  {n m : Nat}
  {color : PreferenceGridVertex n m → Bool}
  {t : PreferenceTriangle n m}
  {chain : PreferenceRightFlagChain color t} :
-- imply
  ∀ (incoming : Fin 3) (hincoming : preferenceTriangleSideActive color t incoming), ∃ (lastTriangle : PreferenceTriangle n m) (lastSide : Fin 3) (hlast : preferenceTriangleSideActive color lastTriangle lastSide), preferenceTriangleOther lastTriangle lastSide = .right ∧ (preferenceGridBoundaryGraph color).Reachable (preferenceSideBoundaryPoint color t incoming hincoming) (preferenceSideBoundaryPoint color lastTriangle lastSide hlast) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PreferenceRightFlagChain.boundaryReachable chain

/--
[preferenceTriangleSideTrue_col_zero_of_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean)
-/
@[path]
private lemma preferenceTriangleSideTrue_col_zero_of_left_eq
  {n m : Nat}
  {color : PreferenceGridVertex n m → Bool}
  {t : PreferenceTriangle n m}
  {k : Fin 3}
-- given
  (hleft : preferenceTriangleOther t k = .left) :
-- imply
  (preferenceTriangleSideTrue color t k).1.val = 0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.preferenceTriangleSideTrue_col_zero_of_left color t k hleft

/--
[preferenceTriangleSideTrue_col_right_of_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean)
-/
@[path]
private lemma preferenceTriangleSideTrue_col_right_of_right_eq
  {n m : Nat}
  {color : PreferenceGridVertex n m → Bool}
  {t : PreferenceTriangle n m}
  {k : Fin 3}
-- given
  (hright : preferenceTriangleOther t k = .right) :
-- imply
  (preferenceTriangleSideTrue color t k).1.val = n := by
-- proof
  apply StatMech.FK.PeriodicPlanar.preferenceTriangleSideTrue_col_right_of_right color t k hright

/--
[preferenceGridBoundary_color_data](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean)
-/
@[path]
private lemma preferenceGridBoundary_color_data_eq
  {n m : Nat}
  {color : PreferenceGridVertex n m → Bool}
  {x : PreferenceGridVertex n m}
-- given
  (hx : x ∈ preferenceGridBoundary color) :
-- imply
  color x = true ∧ ∃ y : PreferenceGridVertex n m, KingAdj (preferenceGridSite x) (preferenceGridSite y) ∧ color y = false := by
-- proof
  apply StatMech.FK.PeriodicPlanar.preferenceGridBoundary_color_data color x hx

/--
[preferenceGridBoundary_reachable_left_right_of_flagCrossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean)
-/
@[path]
private lemma preferenceGridBoundary_reachable_left_right_of_flagCrossing_eq
  {n m : Nat}
  {color : PreferenceGridVertex n m → Bool}
-- given
  (hcross : PreferenceFlagCrossing color) :
-- imply
  ∃ (leftPoint rightPoint : {x // x ∈ preferenceGridBoundary color}), leftPoint.val.1.val = 0 ∧ rightPoint.val.1.val = n ∧ (preferenceGridBoundaryGraph color).Reachable leftPoint rightPoint := by
-- proof
  apply StatMech.FK.PeriodicPlanar.preferenceGridBoundary_reachable_left_right_of_flagCrossing color hcross

/--
[preferenceGridSite_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean)
-/
@[path]
private lemma preferenceGridSite_injective_eq
  {n m : Nat} :
-- imply
  Function.Injective (preferenceGridSite : PreferenceGridVertex n m → Site 2) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.preferenceGridSite_injective

/--
[preferenceGridBoundary_site_mem_inner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean)
-/
@[path]
private lemma preferenceGridBoundary_site_mem_inner_eq
  {n m : Nat}
  {color : PreferenceGridVertex n m → Bool} :
-- imply
  ∀ x : {x // x ∈ preferenceGridBoundary color}, preferenceGridSite (n := n) (m := m) (x : PreferenceGridVertex n m) ∈ preferenceInnerBoundary (preferenceGridRectangle n m) (preferenceGridTrueSet color) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.preferenceGridBoundary_site_mem_inner color

/--
[walk_exists_last_mem_adj_notMem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean)
-/
@[path]
private lemma walk_exists_last_mem_adj_notMem_eq
  {G : SimpleGraph W}
  {Y : Set W}
  {l r : W}
  {p : G.Walk l r}
-- given
  (hl : l ∈ Y)
  (hr : r ∉ Y) :
-- imply
  ∃ x y : W, x ∈ p.support ∧ y ∈ p.support ∧ G.Adj x y ∧ x ∈ Y ∧ y ∉ Y := by
-- proof
  apply StatMech.FK.PeriodicPlanar.walk_exists_last_mem_adj_notMem Y p hl hr

/--
[exists_preference_witness_of_boundary_walk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean)
-/
@[path]
private lemma exists_preference_witness_of_boundary_walk_eq
  {rectangle X Y : Set (Site 2)}
  {l r : {x // x ∈ preferenceInnerBoundary rectangle X}}
  {p : (preferenceBoundaryGraph rectangle X).Walk l r}
-- given
  (hl : (l : Site 2) ∈ Y)
  (hr : (r : Site 2) ∉ Y) :
-- imply
  ∃ x ∈ rectangle, x ∈ X ∧ x ∈ Y ∧ (∃ x' ∈ rectangle, KingAdj x x' ∧ x' ∉ X) ∧ (∃ x'' ∈ rectangle, KingAdj x x'' ∧ x'' ∉ Y) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.exists_preference_witness_of_boundary_walk rectangle X Y p hl hr

/--
[exists_preference_witness_of_grid_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean)
-/
@[path]
private lemma exists_preference_witness_of_grid_boundary_eq
  {n m : Nat}
  {color : PreferenceGridVertex n m → Bool}
  {Y : Set (Site 2)}
-- given
  (hn : 0 < n)
  (hbottom : ∀ i : Fin (n + 1), color (i, 0) = true)
  (htop : ∀ i : Fin (n + 1), color (i, Fin.last m) = false)
  (hYleft : ∀ x : {x // x ∈ preferenceGridBoundary color}, x.val.1.val = 0 → (preferenceGridBoundaryToSite color x : Site 2) ∈ Y)
  (hYright : ∀ x : {x // x ∈ preferenceGridBoundary color}, x.val.1.val = n → (preferenceGridBoundaryToSite color x : Site 2) ∉ Y) :
-- imply
  ∃ x ∈ preferenceGridRectangle n m, x ∈ preferenceGridTrueSet color ∧ x ∈ Y ∧ (∃ x' ∈ preferenceGridRectangle n m, KingAdj x x' ∧ x' ∉ preferenceGridTrueSet color) ∧ (∃ x'' ∈ preferenceGridRectangle n m, KingAdj x x'' ∧ x'' ∉ Y) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.exists_preference_witness_of_grid_boundary color hn hbottom htop Y hYleft hYright


-- created on 2026-10-23
