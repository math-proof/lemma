import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneCage.Part9
open Filter MeasureTheory Set SimpleGraph Topology StatMech StatMech.FK StatMech.FK.PeriodicPlanar StatMech.FK.PeriodicPlanar.ContinuousHalfPlaneCrosscut StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair


/--
[exists_parameter_coord_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean)
-/
@[path]
private lemma exists_parameter_coord_eq_eq
  [DecidableEq V]
  [Countable V]
  {start finish : Fin 2 → Real}
  {gamma : Path start finish}
  {i : Fin 2}
  {a : Real}
-- given
  (hstart : start i ≤ a)
  (hfinish : a ≤ finish i) :
-- imply
  ∃ t : unitInterval, gamma t i = a := by
-- proof
  apply StatMech.FK.PeriodicPlanar.ContinuousHalfPlaneCrosscut.exists_parameter_coord_eq gamma i a hstart hfinish

/--
[exists_parameter_coord_eq_of_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean)
-/
@[path]
private lemma exists_parameter_coord_eq_of_ge_eq
  [DecidableEq V]
  [Countable V]
  {start finish : Fin 2 → Real}
  {gamma : Path start finish}
  {i : Fin 2}
  {a : Real}
-- given
  (hstart : a ≤ start i)
  (hfinish : finish i ≤ a) :
-- imply
  ∃ t : unitInterval, gamma t i = a := by
-- proof
  apply StatMech.FK.PeriodicPlanar.ContinuousHalfPlaneCrosscut.exists_parameter_coord_eq_of_ge gamma i a hstart hfinish

/--
[exists_first_parameter_coord_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean)
-/
@[path]
private lemma exists_first_parameter_coord_eq_eq
  [DecidableEq V]
  [Countable V]
  {start finish : Fin 2 → Real}
  {gamma : Path start finish}
  {i : Fin 2}
  {a : Real}
-- given
  (hne : ∃ u : unitInterval, gamma u i = a) :
-- imply
  ∃ t : unitInterval, gamma t i = a ∧ ∀ u : unitInterval, gamma u i = a → t ≤ u := by
-- proof
  apply StatMech.FK.PeriodicPlanar.ContinuousHalfPlaneCrosscut.exists_first_parameter_coord_eq gamma i a hne

/--
[exists_last_parameter_coord_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean)
-/
@[path]
private lemma exists_last_parameter_coord_eq_eq
  [DecidableEq V]
  [Countable V]
  {start finish : Fin 2 → Real}
  {gamma : Path start finish}
  {i : Fin 2}
  {a : Real}
-- given
  (hne : ∃ u : unitInterval, gamma u i = a) :
-- imply
  ∃ t : unitInterval, gamma t i = a ∧ ∀ u : unitInterval, gamma u i = a → u ≤ t := by
-- proof
  apply StatMech.FK.PeriodicPlanar.ContinuousHalfPlaneCrosscut.exists_last_parameter_coord_eq gamma i a hne

/--
[exists_first_line_contact_suffix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean)
-/
@[path]
private lemma exists_first_line_contact_suffix_eq
  [DecidableEq V]
  [Countable V]
  {start finish : Fin 2 → Real}
  {gamma : Path start finish}
  {i : Fin 2}
  {a : Real}
-- given
  (hstart : start i ≤ a)
  (hfinish : a ≤ finish i) :
-- imply
  ∃ t : unitInterval, gamma t i = a ∧ (∀ u : unitInterval, gamma u i = a → t ≤ u) ∧ Set.range (gamma.subpath t 1) ⊆ Set.range gamma := by
-- proof
  apply StatMech.FK.PeriodicPlanar.ContinuousHalfPlaneCrosscut.exists_first_line_contact_suffix gamma i a hstart hfinish

/--
[exists_last_line_contact_prefix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean)
-/
@[path]
private lemma exists_last_line_contact_prefix_eq
  [DecidableEq V]
  [Countable V]
  {start finish : Fin 2 → Real}
  {gamma : Path start finish}
  {i : Fin 2}
  {a : Real}
-- given
  (hstart : start i ≤ a)
  (hfinish : a ≤ finish i) :
-- imply
  ∃ t : unitInterval, gamma t i = a ∧ (∀ u : unitInterval, gamma u i = a → u ≤ t) ∧ Set.range (gamma.subpath 0 t) ⊆ Set.range gamma := by
-- proof
  apply StatMech.FK.PeriodicPlanar.ContinuousHalfPlaneCrosscut.exists_last_line_contact_prefix gamma i a hstart hfinish

/--
[affinePath_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean)
-/
@[path]
private lemma affinePath_apply_eq
  [DecidableEq V]
  [Countable V]
  {x y : Fin 2 → Real}
  {t : unitInterval}
  {i : Fin 2} :
-- imply
  affinePath x y t i = (1 - (t : Real)) * x i + (t : Real) * y i := by
-- proof
  apply StatMech.FK.PeriodicPlanar.ContinuousHalfPlaneCrosscut.affinePath_apply x y t i

/--
[horizontalPrefix_apply_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean)
-/
@[path]
private lemma horizontalPrefix_apply_one_eq
  [DecidableEq V]
  [Countable V]
  {a : Real}
  {root : Fin 2 → Real}
  {t : unitInterval} :
-- imply
  horizontalPrefix a root t 1 = root 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.ContinuousHalfPlaneCrosscut.horizontalPrefix_apply_one a root t

/--
[horizontalPrefix_disjoint_of_range_below](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean)
-/
@[path]
private lemma horizontalPrefix_disjoint_of_range_below_eq
  [DecidableEq V]
  [Countable V]
  {x y root : Fin 2 → Real}
  {a : Real}
  {gamma : Path x y}
-- given
  (hbelow : ∀ z ∈ Set.range gamma, z 1 < root 1) :
-- imply
  Disjoint (Set.range (horizontalPrefix a root)) (Set.range gamma) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.ContinuousHalfPlaneCrosscut.horizontalPrefix_disjoint_of_range_below a gamma hbelow

/--
[horizontalPrefix_disjoint_of_range_above](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean)
-/
@[path]
private lemma horizontalPrefix_disjoint_of_range_above_eq
  [DecidableEq V]
  [Countable V]
  {x y root : Fin 2 → Real}
  {a : Real}
  {gamma : Path x y}
-- given
  (habove : ∀ z ∈ Set.range gamma, root 1 < z 1) :
-- imply
  Disjoint (Set.range (horizontalPrefix a root)) (Set.range gamma) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.ContinuousHalfPlaneCrosscut.horizontalPrefix_disjoint_of_range_above a gamma habove

/--
[disjoint_of_coord_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean)
-/
@[path]
private lemma disjoint_of_coord_lt_eq
  [DecidableEq V]
  [Countable V]
  {A C : Set (Fin 2 → Real)}
  {i : Fin 2}
-- given
  (hsep : ∀ x ∈ A, ∀ y ∈ C, x i < y i) :
-- imply
  Disjoint A C := by
-- proof
  apply StatMech.FK.PeriodicPlanar.ContinuousHalfPlaneCrosscut.disjoint_of_coord_lt i hsep

/--
[horizontalPrefix_coord_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean)
-/
@[path]
private lemma horizontalPrefix_coord_lt_eq
  [DecidableEq V]
  [Countable V]
  {a R : Real}
  {root : Fin 2 → Real}
-- given
  (ha : a < R)
  (hroot : root 0 < R) :
-- imply
  ∀ z ∈ Set.range (horizontalPrefix a root), z 0 < R := by
-- proof
  apply StatMech.FK.PeriodicPlanar.ContinuousHalfPlaneCrosscut.horizontalPrefix_coord_lt ha hroot

/--
[rectangleMargin_nonneg_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean)
-/
@[path]
private lemma rectangleMargin_nonneg_iff_eq
  [DecidableEq V]
  [Countable V]
  {a b c d : Real}
  {z : Fin 2 → Real} :
-- imply
  0 ≤ rectangleMargin a b c d z ↔ ContinuousRectangleCrossing.InRectangle a b c d z := by
-- proof
  apply StatMech.FK.PeriodicPlanar.ContinuousHalfPlaneCrosscut.rectangleMargin_nonneg_iff a b c d z

/--
[exists_first_rectangle_exit_prefix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean)
-/
@[path]
private lemma exists_first_rectangle_exit_prefix_eq
  [DecidableEq V]
  [Countable V]
  {start finish : Fin 2 → Real}
  {gamma : Path start finish}
  {a b c d : Real}
-- given
  (hstart : a < start 0 ∧ start 0 < b ∧ c < start 1 ∧ start 1 < d)
  (hfinish : ¬ ContinuousRectangleCrossing.InRectangle a b c d finish) :
-- imply
  ∃ t : unitInterval, rectangleMargin a b c d (gamma t) = 0 ∧ Set.range (gamma.subpath 0 t) ⊆ {z | ContinuousRectangleCrossing.InRectangle a b c d z} ∧ Set.range (gamma.subpath 0 t) ⊆ Set.range gamma ∧ (gamma t 0 = a ∨ gamma t 0 = b ∨ gamma t 1 = c ∨ gamma t 1 = d) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.ContinuousHalfPlaneCrosscut.exists_first_rectangle_exit_prefix gamma hstart hfinish

/--
[leftCrosscut_intersects_leftRightPath_of_left_between](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean)
-/
@[path]
private lemma leftCrosscut_intersects_leftRightPath_of_left_between_eq
  [DecidableEq V]
  [Countable V]
  {a b c d : Real}
  {lo hi start finish : Fin 2 → Real}
  {crosscut : Path lo hi}
  {escape : Path start finish}
-- given
  (hab : a < b)
  (hcd : c < d)
  (hcrossRect : Set.range crosscut ⊆ {p | ContinuousRectangleCrossing.InRectangle a b c d p})
  (hescapeRect : Set.range escape ⊆ {p | ContinuousRectangleCrossing.InRectangle a b c d p})
  (hloX : lo 0 = a)
  (hhiX : hi 0 = a)
  (hstartX : start 0 = a)
  (hfinishX : finish 0 = b)
  (hloY : c ≤ lo 1)
  (hhiY : hi 1 ≤ d)
  (hescapeLeftBetween : ∀ p ∈ Set.range escape, p 0 = a → lo 1 < p 1 ∧ p 1 < hi 1) :
-- imply
  (Set.range escape ∩ Set.range crosscut).Nonempty := by
-- proof
  apply StatMech.FK.PeriodicPlanar.ContinuousHalfPlaneCrosscut.leftCrosscut_intersects_leftRightPath_of_left_between hab hcd crosscut escape hcrossRect hescapeRect hloX hhiX hstartX hfinishX hloY hhiY hescapeLeftBetween

/--
[leftCrosscut_intersects_leftTopPath_of_left_between](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean)
-/
@[path]
private lemma leftCrosscut_intersects_leftTopPath_of_left_between_eq
  [DecidableEq V]
  [Countable V]
  {a b c d : Real}
  {lo hi start finish : Fin 2 → Real}
  {crosscut : Path lo hi}
  {escape : Path start finish}
-- given
  (hab : a < b)
  (hcd : c < d)
  (hcrossRect : Set.range crosscut ⊆ {p | ContinuousRectangleCrossing.InRectangle a b c d p})
  (hescapeRect : Set.range escape ⊆ {p | ContinuousRectangleCrossing.InRectangle a b c d p})
  (hloX : lo 0 = a)
  (hhiX : hi 0 = a)
  (hstartX : start 0 = a)
  (hfinishY : finish 1 = d)
  (hfinishX : a < finish 0)
  (hloY : c ≤ lo 1)
  (hhiY : hi 1 ≤ d)
  (hescapeLeftBetween : ∀ p ∈ Set.range escape, p 0 = a → lo 1 < p 1 ∧ p 1 < hi 1)
  (hcrossBelowTop : ∀ t : unitInterval, crosscut t 1 < d) :
-- imply
  (Set.range escape ∩ Set.range crosscut).Nonempty := by
-- proof
  apply StatMech.FK.PeriodicPlanar.ContinuousHalfPlaneCrosscut.leftCrosscut_intersects_leftTopPath_of_left_between hab hcd crosscut escape hcrossRect hescapeRect hloX hhiX hstartX hfinishY hfinishX hloY hhiY hescapeLeftBetween hcrossBelowTop

/--
[leftCrosscut_intersects_leftBottomPath_of_left_between](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean)
-/
@[path]
private lemma leftCrosscut_intersects_leftBottomPath_of_left_between_eq
  [DecidableEq V]
  [Countable V]
  {a b c d : Real}
  {lo hi start finish : Fin 2 → Real}
  {crosscut : Path lo hi}
  {escape : Path start finish}
-- given
  (hab : a < b)
  (hcd : c < d)
  (hcrossRect : Set.range crosscut ⊆ {p | ContinuousRectangleCrossing.InRectangle a b c d p})
  (hescapeRect : Set.range escape ⊆ {p | ContinuousRectangleCrossing.InRectangle a b c d p})
  (hloX : lo 0 = a)
  (hhiX : hi 0 = a)
  (hstartX : start 0 = a)
  (hfinishY : finish 1 = c)
  (hfinishX : a < finish 0)
  (hloY : c ≤ lo 1)
  (hhiY : hi 1 ≤ d)
  (hescapeLeftBetween : ∀ p ∈ Set.range escape, p 0 = a → lo 1 < p 1 ∧ p 1 < hi 1)
  (hcrossAboveBottom : ∀ t : unitInterval, c < crosscut t 1) :
-- imply
  (Set.range escape ∩ Set.range crosscut).Nonempty := by
-- proof
  apply StatMech.FK.PeriodicPlanar.ContinuousHalfPlaneCrosscut.leftCrosscut_intersects_leftBottomPath_of_left_between hab hcd crosscut escape hcrossRect hescapeRect hloX hhiX hstartX hfinishY hfinishX hloY hhiY hescapeLeftBetween hcrossAboveBottom

/--
[attachedCrosscut_intersection_reduces_to_core](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean)
-/
@[path]
private lemma attachedCrosscut_intersection_reduces_to_core_eq
  [DecidableEq V]
  [Countable V]
  {lo hi x y start finish : Fin 2 → Real}
  {lower : Path lo x}
  {core : Path x y}
  {upper : Path y hi}
  {escape : Path start finish}
-- given
  (hinter : (Set.range escape ∩ Set.range (lower.trans (core.trans upper))).Nonempty)
  (hlower : Disjoint (Set.range escape) (Set.range lower))
  (hupper : Disjoint (Set.range escape) (Set.range upper)) :
-- imply
  (Set.range escape ∩ Set.range core).Nonempty := by
-- proof
  apply StatMech.FK.PeriodicPlanar.ContinuousHalfPlaneCrosscut.attachedCrosscut_intersection_reduces_to_core lower core upper escape hinter hlower hupper

/--
[doublyAttached_intersection_reduces_to_cores](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean)
-/
@[path]
private lemma doublyAttached_intersection_reduces_to_cores_eq
  [DecidableEq V]
  [Countable V]
  {plo px py phi estart eroot efinish : Fin 2 → Real}
  {plower : Path plo px}
  {pcore : Path px py}
  {pupper : Path py phi}
  {eprefix : Path estart eroot}
  {ecore : Path eroot efinish}
-- given
  (hinter : (Set.range (eprefix.trans ecore) ∩ Set.range (plower.trans (pcore.trans pupper))).Nonempty)
  (hPrefixLower : Disjoint (Set.range eprefix) (Set.range plower))
  (hPrefixCore : Disjoint (Set.range eprefix) (Set.range pcore))
  (hPrefixUpper : Disjoint (Set.range eprefix) (Set.range pupper))
  (hCoreLower : Disjoint (Set.range ecore) (Set.range plower))
  (hCoreUpper : Disjoint (Set.range ecore) (Set.range pupper)) :
-- imply
  (Set.range ecore ∩ Set.range pcore).Nonempty := by
-- proof
  apply StatMech.FK.PeriodicPlanar.ContinuousHalfPlaneCrosscut.doublyAttached_intersection_reduces_to_cores plower pcore pupper eprefix ecore hinter hPrefixLower hPrefixCore hPrefixUpper hCoreLower hCoreUpper

/--
[leftCrosscut_intersects_leftRightPath](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean)
-/
@[path]
private lemma leftCrosscut_intersects_leftRightPath_eq
  [DecidableEq V]
  [Countable V]
  {a b c d : Real}
  {lo hi start finish : Fin 2 → Real}
  {crosscut : Path lo hi}
  {escape : Path start finish}
-- given
  (hab : a < b)
  (hcd : c < d)
  (hcrossRect : Set.range crosscut ⊆ {p | ContinuousRectangleCrossing.InRectangle a b c d p})
  (hescapeRect : Set.range escape ⊆ {p | ContinuousRectangleCrossing.InRectangle a b c d p})
  (hloX : lo 0 = a)
  (hhiX : hi 0 = a)
  (hstartX : start 0 = a)
  (hfinishX : finish 0 = b)
  (hloY : c ≤ lo 1)
  (hhiY : hi 1 ≤ d)
  (horderLo : lo 1 < start 1)
  (horderHi : start 1 < hi 1)
  (hescapeLeft : ∀ p ∈ Set.range escape, p 0 = a → p = start) :
-- imply
  (Set.range escape ∩ Set.range crosscut).Nonempty := by
-- proof
  apply StatMech.FK.PeriodicPlanar.ContinuousHalfPlaneCrosscut.leftCrosscut_intersects_leftRightPath hab hcd crosscut escape hcrossRect hescapeRect hloX hhiX hstartX hfinishX hloY hhiY horderLo horderHi hescapeLeft

/--
[leftCrosscut_intersects_leftTopPath](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean)
-/
@[path]
private lemma leftCrosscut_intersects_leftTopPath_eq
  [DecidableEq V]
  [Countable V]
  {a b c d : Real}
  {lo hi start finish : Fin 2 → Real}
  {crosscut : Path lo hi}
  {escape : Path start finish}
-- given
  (hab : a < b)
  (hcd : c < d)
  (hcrossRect : Set.range crosscut ⊆ {p | ContinuousRectangleCrossing.InRectangle a b c d p})
  (hescapeRect : Set.range escape ⊆ {p | ContinuousRectangleCrossing.InRectangle a b c d p})
  (hloX : lo 0 = a)
  (hhiX : hi 0 = a)
  (hstartX : start 0 = a)
  (hfinishY : finish 1 = d)
  (hfinishX : a < finish 0)
  (hloY : c ≤ lo 1)
  (hhiY : hi 1 ≤ d)
  (horderLo : lo 1 < start 1)
  (horderHi : start 1 < hi 1)
  (hescapeLeft : ∀ p ∈ Set.range escape, p 0 = a → p = start)
  (hcrossBelowTop : ∀ t : unitInterval, crosscut t 1 < d) :
-- imply
  (Set.range escape ∩ Set.range crosscut).Nonempty := by
-- proof
  apply StatMech.FK.PeriodicPlanar.ContinuousHalfPlaneCrosscut.leftCrosscut_intersects_leftTopPath hab hcd crosscut escape hcrossRect hescapeRect hloX hhiX hstartX hfinishY hfinishX hloY hhiY horderLo horderHi hescapeLeft hcrossBelowTop

/--
[leftCrosscut_intersects_leftBottomPath](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean)
-/
@[path]
private lemma leftCrosscut_intersects_leftBottomPath_eq
  [DecidableEq V]
  [Countable V]
  {a b c d : Real}
  {lo hi start finish : Fin 2 → Real}
  {crosscut : Path lo hi}
  {escape : Path start finish}
-- given
  (hab : a < b)
  (hcd : c < d)
  (hcrossRect : Set.range crosscut ⊆ {p | ContinuousRectangleCrossing.InRectangle a b c d p})
  (hescapeRect : Set.range escape ⊆ {p | ContinuousRectangleCrossing.InRectangle a b c d p})
  (hloX : lo 0 = a)
  (hhiX : hi 0 = a)
  (hstartX : start 0 = a)
  (hfinishY : finish 1 = c)
  (hfinishX : a < finish 0)
  (hloY : c ≤ lo 1)
  (hhiY : hi 1 ≤ d)
  (horderLo : lo 1 < start 1)
  (horderHi : start 1 < hi 1)
  (hescapeLeft : ∀ p ∈ Set.range escape, p 0 = a → p = start)
  (hcrossAboveBottom : ∀ t : unitInterval, c < crosscut t 1) :
-- imply
  (Set.range escape ∩ Set.range crosscut).Nonempty := by
-- proof
  apply StatMech.FK.PeriodicPlanar.ContinuousHalfPlaneCrosscut.leftCrosscut_intersects_leftBottomPath hab hcd crosscut escape hcrossRect hescapeRect hloX hhiX hstartX hfinishY hfinishX hloY hhiY horderLo horderHi hescapeLeft hcrossAboveBottom

/--
[PeriodicPlaneEmbedding.simpleWalkArc_coord_lower_of_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean)
-/
@[path]
private lemma simpleWalkArc_coord_lower_of_support_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {B r : Real}
  {i : Fin 2}
  {x y : V}
  {p : P.graph.Walk x y}
-- given
  (hB0 : 0 ≤ B)
  (hB : ∀ {u v : V} (huv : P.graph.Adj u v) (t) (i : Fin 2), |E.coordinates (E.edgeArc huv t - E.vertex u) i| ≤ B)
  (hp : ∀ v ∈ p.support, r ≤ E.vertexCoord v i) :
-- imply
  ∀ t : unitInterval, r - B ≤ E.coordinates (E.simpleWalkArc p t) i := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.simpleWalkArc_coord_lower_of_support E hB0 hB i p hp

/--
[PeriodicPlaneEmbedding.simpleWalkArc_coord_upper_of_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean)
-/
@[path]
private lemma simpleWalkArc_coord_upper_of_support_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {B r : Real}
  {i : Fin 2}
  {x y : V}
  {p : P.graph.Walk x y}
-- given
  (hB0 : 0 ≤ B)
  (hB : ∀ {u v : V} (huv : P.graph.Adj u v) (t) (i : Fin 2), |E.coordinates (E.edgeArc huv t - E.vertex u) i| ≤ B)
  (hp : ∀ v ∈ p.support, E.vertexCoord v i ≤ r) :
-- imply
  ∀ t : unitInterval, E.coordinates (E.simpleWalkArc p t) i ≤ r + B := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.simpleWalkArc_coord_upper_of_support E hB0 hB i p hp

/--
[PeriodicPlaneEmbedding.exists_boundary_line_attachments](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean)
-/
@[path]
private lemma exists_boundary_line_attachments_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {B r c d : Real}
  {b u : V}
-- given
  (hB0 : 0 ≤ B)
  (hB : ∀ {v w : V} (hvw : P.graph.Adj v w) (t) (i : Fin 2), |E.coordinates (E.edgeArc hvw t - E.vertex v) i| ≤ B)
  (hb : b ∈ E.lowerBoundaryRayVertices r c)
  (hu : u ∈ E.upperBoundaryRayVertices r d) :
-- imply
  ∃ lo hi : Fin 2 → Real, ∃ lower : Path lo (E.coordinates (E.vertex b)), ∃ upper : Path (E.coordinates (E.vertex u)) hi, lo 0 = r ∧ hi 0 = r ∧ lo 1 ≤ c + B ∧ d - B ≤ hi 1 ∧ (∀ z ∈ Set.range lower, z 1 ≤ c + B) ∧ (∀ z ∈ Set.range upper, d - B ≤ z 1) ∧ (∀ z ∈ Set.range lower, z 0 < r + 2 * B) ∧ ∀ z ∈ Set.range upper, z 0 < r + 2 * B := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_boundary_line_attachments E hB0 hB hb hu

/--
[PeriodicGraph.exists_open_boundary_walk_of_walk_to_compl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean)
-/
@[path]
private lemma exists_open_boundary_walk_of_walk_to_compl_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {omega : ConfigSpace (Sym2 V)}
  {A : Set V}
  {x y : V}
  {p : (P.openSubgraph omega).Walk x y}
-- given
  (hx : x ∈ A)
  (hy : y ∉ A) :
-- imply
  ∃ b ∈ A, ∃ z : V, (P.openSubgraph omega).Adj b z ∧ z ∉ A ∧ ∃ q : (P.openSubgraph omega).Walk x b, (∀ v ∈ q.support, v ∈ A) ∧ (∀ v ∈ q.support, v ∈ p.support) ∧ z ∈ p.support := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.exists_open_boundary_walk_of_walk_to_compl P omega A p hx hy

/--
[PeriodicPlaneEmbedding.infiniteOpenBoundaryConnectionTo_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean)
-/
@[path]
private lemma infiniteOpenBoundaryConnectionTo_measurableSet_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {r : Real}
  {S T : Set V} :
-- imply
  MeasurableSet (E.infiniteOpenBoundaryConnectionTo r S T) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.infiniteOpenBoundaryConnectionTo_measurableSet E r S T

/--
[PeriodicPlaneEmbedding.infiniteOpenBoundaryConnectionTo_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean)
-/
@[path]
private lemma infiniteOpenBoundaryConnectionTo_isIncreasing_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {r : Real}
  {S T : Set V} :
-- imply
  IsIncreasing (E.infiniteOpenBoundaryConnectionTo r S T) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.infiniteOpenBoundaryConnectionTo_isIncreasing E r S T

/--
[PeriodicPlaneEmbedding.infiniteOpenBoundaryConnectionTo_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean)
-/
@[path]
private lemma infiniteOpenBoundaryConnectionTo_subset_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {r : Real}
  {S T : Set V} :
-- imply
  E.infiniteOpenBoundaryConnectionTo r S T ⊆ E.infiniteOpenBoundaryConnection r S := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.infiniteOpenBoundaryConnectionTo_subset E r S T

/--
[PeriodicPlaneEmbedding.infiniteOpenBoundaryConnectionTo_configTranslate_vertical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean)
-/
@[path]
private lemma infiniteOpenBoundaryConnectionTo_configTranslate_vertical_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {t : Int}
  {omega : ConfigSpace (Sym2 V)}
  {r : Real}
  {S T : Set V} :
-- imply
  P.configTranslate (verticalShift t) omega ∈ E.infiniteOpenBoundaryConnectionTo r (P.shift (verticalShift t) '' S) (P.shift (verticalShift t) '' T) ↔ omega ∈ E.infiniteOpenBoundaryConnectionTo r S T := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.infiniteOpenBoundaryConnectionTo_configTranslate_vertical E t omega r S T

/--
[PeriodicPlaneEmbedding.infiniteOpenLowerBoundaryConnection_measureReal_vertical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean)
-/
@[path]
private lemma infiniteOpenLowerBoundaryConnection_measureReal_vertical_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {t : Int}
  {r s : Real}
  {S : Set V}
-- given
  (hTI : P.IsTranslationInvariant mu) :
-- imply
  mu.real (E.infiniteOpenBoundaryConnectionTo r (P.shift (verticalShift t) '' S) (E.lowerBoundaryRayVertices r (s + t))) = mu.real (E.infiniteOpenBoundaryConnectionTo r S (E.lowerBoundaryRayVertices r s)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.infiniteOpenLowerBoundaryConnection_measureReal_vertical E mu hTI t r s S

/--
[PeriodicPlaneEmbedding.infiniteOpenUpperBoundaryConnection_measureReal_vertical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean)
-/
@[path]
private lemma infiniteOpenUpperBoundaryConnection_measureReal_vertical_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {t : Int}
  {r s : Real}
  {S : Set V}
-- given
  (hTI : P.IsTranslationInvariant mu) :
-- imply
  mu.real (E.infiniteOpenBoundaryConnectionTo r (P.shift (verticalShift t) '' S) (E.upperBoundaryRayVertices r (s + t))) = mu.real (E.infiniteOpenBoundaryConnectionTo r S (E.upperBoundaryRayVertices r s)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.infiniteOpenUpperBoundaryConnection_measureReal_vertical E mu hTI t r s S

/--
[PeriodicPlaneEmbedding.iUnion_infiniteOpenLowerBoundaryConnection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean)
-/
@[path]
private lemma iUnion_infiniteOpenLowerBoundaryConnection_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {r : Real}
  {S : Set V} :
-- imply
  (⋃ n : Nat, E.infiniteOpenBoundaryConnectionTo r S (E.lowerBoundaryRayVertices r n)) = E.infiniteOpenBoundaryConnection r S := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.iUnion_infiniteOpenLowerBoundaryConnection E r S

/--
[PeriodicPlaneEmbedding.iUnion_infiniteOpenUpperBoundaryConnection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean)
-/
@[path]
private lemma iUnion_infiniteOpenUpperBoundaryConnection_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {r : Real}
  {S : Set V} :
-- imply
  (⋃ n : Nat, E.infiniteOpenBoundaryConnectionTo r S (E.upperBoundaryRayVertices r (-(n : Real)))) = E.infiniteOpenBoundaryConnection r S := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.iUnion_infiniteOpenUpperBoundaryConnection E r S

/--
[exists_measureReal_pos_of_iUnion_measureReal_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean)
-/
@[path]
private lemma exists_measureReal_pos_of_iUnion_measureReal_pos_eq
  [DecidableEq V]
  [Countable V]
  [MeasurableSpace X]
  {mu : Measure X}
  [IsFiniteMeasure mu]
  {A : Nat → Set X}
-- given
  (hpos : 0 < mu.real (⋃ n, A n)) :
-- imply
  ∃ n, 0 < mu.real (A n) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.exists_measureReal_pos_of_iUnion_measureReal_pos mu A hpos

/--
[PeriodicPlaneEmbedding.exists_positive_infiniteOpenLowerBoundaryConnection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean)
-/
@[path]
private lemma exists_positive_infiniteOpenLowerBoundaryConnection_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsFiniteMeasure mu]
  {r : Real}
  {S : Set V}
-- given
  (hpos : 0 < mu.real (E.infiniteOpenBoundaryConnection r S)) :
-- imply
  ∃ n : Nat, 0 < mu.real (E.infiniteOpenBoundaryConnectionTo r S (E.lowerBoundaryRayVertices r n)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_positive_infiniteOpenLowerBoundaryConnection E mu r S hpos

/--
[PeriodicPlaneEmbedding.exists_positive_infiniteOpenUpperBoundaryConnection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean)
-/
@[path]
private lemma exists_positive_infiniteOpenUpperBoundaryConnection_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsFiniteMeasure mu]
  {r : Real}
  {S : Set V}
-- given
  (hpos : 0 < mu.real (E.infiniteOpenBoundaryConnection r S)) :
-- imply
  ∃ n : Nat, 0 < mu.real (E.infiniteOpenBoundaryConnectionTo r S (E.upperBoundaryRayVertices r (-(n : Real)))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_positive_infiniteOpenUpperBoundaryConnection E mu r S hpos

/--
[PeriodicPlaneEmbedding.finiteJoinedBoundaryArmAt_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean)
-/
@[path]
private lemma finiteJoinedBoundaryArmAt_measurableSet_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {r c d : Real}
  {n : Nat}
  {L R : Finset V}
  {b u : V} :
-- imply
  MeasurableSet (E.finiteJoinedBoundaryArmAt r c d n L R b u) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.finiteJoinedBoundaryArmAt_measurableSet E r c d n L R b u

/--
[PeriodicPlaneEmbedding.finiteJoinedBoundaryArmAt_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean)
-/
@[path]
private lemma finiteJoinedBoundaryArmAt_isIncreasing_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {r c d : Real}
  {n : Nat}
  {L R : Finset V}
  {b u : V} :
-- imply
  IsIncreasing (E.finiteJoinedBoundaryArmAt r c d n L R b u) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.finiteJoinedBoundaryArmAt_isIncreasing E r c d n L R b u

/--
[PeriodicPlaneEmbedding.finiteJoinedBoundaryArmEvent_subset_iUnion_at](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean)
-/
@[path]
private lemma finiteJoinedBoundaryArmEvent_subset_iUnion_at_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {r c d : Real}
  {n : Nat}
  {L R : Finset V} :
-- imply
  E.finiteJoinedBoundaryArmEvent r c d n L R ⊆ ⋃ b : V, ⋃ u : V, E.finiteJoinedBoundaryArmAt r c d n L R b u := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.finiteJoinedBoundaryArmEvent_subset_iUnion_at E r c d n L R

/--
[exists_measureReal_pos_of_countable_iUnion_measureReal_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean)
-/
@[path]
private lemma exists_measureReal_pos_of_countable_iUnion_measureReal_pos_eq
  [DecidableEq V]
  [Countable V]
  [MeasurableSpace X]
  [Countable I]
  {mu : Measure X}
  [IsFiniteMeasure mu]
  {A : I → Set X}
-- given
  (hpos : 0 < mu.real (⋃ i, A i)) :
-- imply
  ∃ i, 0 < mu.real (A i) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.exists_measureReal_pos_of_countable_iUnion_measureReal_pos mu A hpos

/--
[PeriodicPlaneEmbedding.exists_positive_finiteJoinedBoundaryArmAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean)
-/
@[path]
private lemma exists_positive_finiteJoinedBoundaryArmAt_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsFiniteMeasure mu]
  {r c d : Real}
  {n : Nat}
  {L R : Finset V}
-- given
  (hpos : 0 < mu.real (E.finiteJoinedBoundaryArmEvent r c d n L R)) :
-- imply
  ∃ b u : V, 0 < mu.real (E.finiteJoinedBoundaryArmAt r c d n L R b u) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_positive_finiteJoinedBoundaryArmAt E mu r c d n L R hpos

/--
[PeriodicPlaneEmbedding.finiteOpenExitedJoinedBoundaryArmEvent_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean)
-/
@[path]
private lemma finiteOpenExitedJoinedBoundaryArmEvent_measurableSet_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {r c d : Real}
  {n : Nat}
  {L R : Finset V} :
-- imply
  MeasurableSet (E.finiteOpenExitedJoinedBoundaryArmEvent r c d n L R) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.finiteOpenExitedJoinedBoundaryArmEvent_measurableSet E r c d n L R

/--
[PeriodicPlaneEmbedding.finiteOpenExitedJoinedBoundaryArmEvent_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean)
-/
@[path]
private lemma finiteOpenExitedJoinedBoundaryArmEvent_isIncreasing_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {r c d : Real}
  {n : Nat}
  {L R : Finset V} :
-- imply
  IsIncreasing (E.finiteOpenExitedJoinedBoundaryArmEvent r c d n L R) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.finiteOpenExitedJoinedBoundaryArmEvent_isIncreasing E r c d n L R

/--
[measureReal_pos_of_forceOpenFinset_preimage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean)
-/
@[path]
private lemma measureReal_pos_of_forceOpenFinset_preimage_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq X]
  [Countable X]
  {mu : Measure (ConfigSpace (Sym2 X))}
  [IsFiniteMeasure mu]
  {F : Finset (Sym2 X)}
  {A B : Set (ConfigSpace (Sym2 X))}
-- given
  (hfe : HasFiniteEnergy mu)
  (hB : MeasurableSet B)
  (hApos : 0 < mu.real A)
  (hsub : A ⊆ forceOpenFinset F ⁻¹' B) :
-- imply
  0 < mu.real B := by
-- proof
  apply StatMech.FK.PeriodicPlanar.measureReal_pos_of_forceOpenFinset_preimage mu hfe F hB hApos hsub

/--
[PeriodicPlaneEmbedding.finiteJoinedBoundaryArmAt_forceOpen_subset_exited](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean)
-/
@[path]
private lemma finiteJoinedBoundaryArmAt_forceOpen_subset_exited_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {r c d : Real}
  {n : Nat}
  {L R : Finset V}
  {b u z w : V}
-- given
  (hbz : P.graph.Adj b z)
  (hz : z ∉ E.rightHalfPlaneVertices r)
  (huw : P.graph.Adj u w)
  (hw : w ∉ E.rightHalfPlaneVertices r) :
-- imply
  E.finiteJoinedBoundaryArmAt r c d n L R b u ⊆ forceOpenFinset {s(b, z), s(u, w)} ⁻¹' E.finiteOpenExitedJoinedBoundaryArmEvent r c d n L R := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.finiteJoinedBoundaryArmAt_forceOpen_subset_exited E hbz hz huw hw

/--
[PeriodicPlaneEmbedding.finiteOpenExitedJoinedBoundaryArmEvent_measureReal_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean)
-/
@[path]
private lemma finiteOpenExitedJoinedBoundaryArmEvent_measureReal_pos_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsFiniteMeasure mu]
  {r c d : Real}
  {n : Nat}
  {L R : Finset V}
-- given
  (hfe : HasFiniteEnergy mu)
  (hpos : 0 < mu.real (E.finiteJoinedBoundaryArmEvent r c d n L R)) :
-- imply
  0 < mu.real (E.finiteOpenExitedJoinedBoundaryArmEvent r c d n L R) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.finiteOpenExitedJoinedBoundaryArmEvent_measureReal_pos E mu hfe r c d n L R hpos

/--
[PeriodicPlaneEmbedding.exists_positive_finiteOpenExitedJoinedBoundaryArmEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean)
-/
@[path]
private lemma exists_positive_finiteOpenExitedJoinedBoundaryArmEvent_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {r : Real}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hfe : HasFiniteEnergy mu) :
-- imply
  ∃ L U : Finset V, ∃ n : Nat, 0 < mu.real (E.finiteOpenExitedJoinedBoundaryArmEvent r 0 1 n L U) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_positive_finiteOpenExitedJoinedBoundaryArmEvent E mu hFKG hTI hunique hfe r

/--
[PeriodicPlaneEmbedding.finiteOpenExitedJoinedBoundaryArmEvent_openWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean)
-/
@[path]
private lemma finiteOpenExitedJoinedBoundaryArmEvent_openWalk_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {omega : ConfigSpace (Sym2 V)}
  {r c d : Real}
  {n : Nat}
  {L R : Finset V}
-- given
  (h : omega ∈ E.finiteOpenExitedJoinedBoundaryArmEvent r c d n L R) :
-- imply
  ∃ b ∈ E.lowerBoundaryRayVertices r c, ∃ z : V, z ∉ E.rightHalfPlaneVertices r ∧ ∃ u ∈ E.upperBoundaryRayVertices r d, ∃ w : V, w ∉ E.rightHalfPlaneVertices r ∧ ∃ q : (P.openSubgraph omega).Walk z w, b ∈ q.support ∧ u ∈ q.support ∧ ∀ v ∈ q.support, v = z ∨ v = w ∨ v ∈ E.rightHalfPlaneVertices r := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.finiteOpenExitedJoinedBoundaryArmEvent_openWalk E h

/--
[PeriodicPlaneEmbedding.rightHalfPlaneBoundaryHasInfiniteCluster_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean)
-/
@[path]
private lemma rightHalfPlaneBoundaryHasInfiniteCluster_measurableSet_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {r : Real} :
-- imply
  MeasurableSet (E.rightHalfPlaneBoundaryHasInfiniteCluster r) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rightHalfPlaneBoundaryHasInfiniteCluster_measurableSet E r

/--
[PeriodicGraph.clusterWithinSet_infinite_of_connectedWithinSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean)
-/
@[path]
private lemma clusterWithinSet_infinite_of_connectedWithinSet_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {omega : ConfigSpace (Sym2 V)}
  {A : Set V}
  {x b : V}
-- given
  (hinfinite : (P.clusterWithinSet omega A x).Infinite)
  (hxb : omega ∈ P.connectedWithinSet A x b) :
-- imply
  (P.clusterWithinSet omega A b).Infinite := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.clusterWithinSet_infinite_of_connectedWithinSet P hinfinite hxb

/--
[PeriodicPlaneEmbedding.unique_halfPlane_outside_subset_boundaryInfinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean)
-/
@[path]
private lemma unique_halfPlane_outside_subset_boundaryInfinite_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {r : Real}
  {T : Set V}
-- given
  (hT : T ⊆ (E.rightHalfPlaneVertices r)ᶜ) :
-- imply
  {omega : ConfigSpace (Sym2 V) | P.HasUniqueInfiniteCluster omega} ∩ (E.rightHalfPlaneHasInfiniteCluster r ∩ P.setHitsInfinite T) ⊆ E.rightHalfPlaneBoundaryHasInfiniteCluster r := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.unique_halfPlane_outside_subset_boundaryInfinite E r T hT

/--
[PeriodicPlaneEmbedding.rightHalfPlaneBoundaryHasInfiniteCluster_measure_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean)
-/
@[path]
private lemma rightHalfPlaneBoundaryHasInfiniteCluster_measure_eq_one_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {r : Real}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hhalf : mu (E.rightHalfPlaneHasInfiniteCluster r) = 1) :
-- imply
  mu (E.rightHalfPlaneBoundaryHasInfiniteCluster r) = 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rightHalfPlaneBoundaryHasInfiniteCluster_measure_eq_one E mu hTI hunique r hhalf

/--
[PeriodicPlaneEmbedding.rightHalfPlaneBoundaryBandHasInfiniteCluster_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean)
-/
@[path]
private lemma rightHalfPlaneBoundaryBandHasInfiniteCluster_measurableSet_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {r c d : Real} :
-- imply
  MeasurableSet (E.rightHalfPlaneBoundaryBandHasInfiniteCluster r c d) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rightHalfPlaneBoundaryBandHasInfiniteCluster_measurableSet E r c d

/--
[PeriodicPlaneEmbedding.iUnion_boundaryBandHasInfiniteCluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean)
-/
@[path]
private lemma iUnion_boundaryBandHasInfiniteCluster_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {r : Real} :
-- imply
  (⋃ n : Nat, E.rightHalfPlaneBoundaryBandHasInfiniteCluster r (-(n : Real)) n) = E.rightHalfPlaneBoundaryHasInfiniteCluster r := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.iUnion_boundaryBandHasInfiniteCluster E r

/--
[PeriodicPlaneEmbedding.exists_positive_boundaryBandHasInfiniteCluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean)
-/
@[path]
private lemma exists_positive_boundaryBandHasInfiniteCluster_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {r : Real}
-- given
  (hone : mu (E.rightHalfPlaneBoundaryHasInfiniteCluster r) = 1) :
-- imply
  ∃ n : Nat, 0 < mu.real (E.rightHalfPlaneBoundaryBandHasInfiniteCluster r (-(n : Real)) n) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_positive_boundaryBandHasInfiniteCluster E mu r hone

/--
[no_open_dual_escape_of_attached_simpleCrosscut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean)
-/
@[path]
private lemma no_open_dual_escape_of_attached_simpleCrosscut_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {D : PeriodicPlanarDualPair P Pdual}
  {omega : ConfigSpace (Sym2 V)}
  {x y : V}
  {s t : W}
  {p : P.graph.Walk x y}
  {q : Pdual.graph.Walk s t}
  {a b c d : Real}
  {lo hi : Fin 2 → Real}
  {lower : Path lo (D.primalEmbedding.coordinates (D.primalEmbedding.vertex x))}
  {upper : Path (D.primalEmbedding.coordinates (D.primalEmbedding.vertex y)) hi}
-- given
  (hp : ¬ p.Nil)
  (hq : ¬ q.Nil)
  (hpopen : ∀ {u v : V}, s(u, v) ∈ p.edges → omega s(u, v) = true)
  (hqopen : ∀ {u v : W}, s(u, v) ∈ q.edges → dualConfigEquiv D.edgeDual omega s(u, v) = true)
  (hab : a < b)
  (hcd : c < d)
  (hcrossRect : Set.range (lower.trans (((D.primalEmbedding.simpleWalkArc p).map D.primalEmbedding.coordinates.continuous).trans upper)) ⊆ {z | ContinuousRectangleCrossing.InRectangle a b c d z})
  (hescapeRect : Set.range ((D.dualEmbedding.simpleWalkArc q).map D.dualEmbedding.coordinates.continuous) ⊆ {z | ContinuousRectangleCrossing.InRectangle a b c d z})
  (hloX : lo 0 = a)
  (hhiX : hi 0 = a)
  (hstartX : D.dualEmbedding.vertexCoord s 0 = a)
  (hloY : c ≤ lo 1)
  (hhiY : hi 1 ≤ d)
  (hescapeLeftBetween : ∀ z ∈ Set.range ((D.dualEmbedding.simpleWalkArc q).map D.dualEmbedding.coordinates.continuous), z 0 = a → lo 1 < z 1 ∧ z 1 < hi 1)
  (hlower : Disjoint (Set.range ((D.dualEmbedding.simpleWalkArc q).map D.dualEmbedding.coordinates.continuous)) (Set.range lower))
  (hupper : Disjoint (Set.range ((D.dualEmbedding.simpleWalkArc q).map D.dualEmbedding.coordinates.continuous)) (Set.range upper))
  (hexit : D.dualEmbedding.vertexCoord t 0 = b ∨ (D.dualEmbedding.vertexCoord t 1 = d ∧ a < D.dualEmbedding.vertexCoord t 0 ∧ ∀ u : unitInterval, (lower.trans (((D.primalEmbedding.simpleWalkArc p).map D.primalEmbedding.coordinates.continuous).trans upper)) u 1 < d) ∨ (D.dualEmbedding.vertexCoord t 1 = c ∧ a < D.dualEmbedding.vertexCoord t 0 ∧ ∀ u : unitInterval, c < (lower.trans (((D.primalEmbedding.simpleWalkArc p).map D.primalEmbedding.coordinates.continuous).trans upper)) u 1)) :
-- imply
  False := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.no_open_dual_escape_of_attached_simpleCrosscut D omega p q hp hq hpopen hqopen hab hcd lower upper hcrossRect hescapeRect hloX hhiX hstartX hloY hhiY hescapeLeftBetween hlower hupper hexit

/--
[no_open_dual_escape_of_doublyAttached_simpleCrosscut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean)
-/
@[path]
private lemma no_open_dual_escape_of_doublyAttached_simpleCrosscut_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {D : PeriodicPlanarDualPair P Pdual}
  {omega : ConfigSpace (Sym2 V)}
  {x y : V}
  {s t : W}
  {p : P.graph.Walk x y}
  {q : Pdual.graph.Walk s t}
  {a b c d : Real}
  {lo hi estart : Fin 2 → Real}
  {lower : Path lo (D.primalEmbedding.coordinates (D.primalEmbedding.vertex x))}
  {upper : Path (D.primalEmbedding.coordinates (D.primalEmbedding.vertex y)) hi}
  {eprefix : Path estart (D.dualEmbedding.coordinates (D.dualEmbedding.vertex s))}
-- given
  (hp : ¬ p.Nil)
  (hq : ¬ q.Nil)
  (hpopen : ∀ {u v : V}, s(u, v) ∈ p.edges → omega s(u, v) = true)
  (hqopen : ∀ {u v : W}, s(u, v) ∈ q.edges → dualConfigEquiv D.edgeDual omega s(u, v) = true)
  (hab : a < b)
  (hcd : c < d)
  (hcrossRect : Set.range (lower.trans (((D.primalEmbedding.simpleWalkArc p).map D.primalEmbedding.coordinates.continuous).trans upper)) ⊆ {z | ContinuousRectangleCrossing.InRectangle a b c d z})
  (hescapeRect : Set.range (eprefix.trans ((D.dualEmbedding.simpleWalkArc q).map D.dualEmbedding.coordinates.continuous)) ⊆ {z | ContinuousRectangleCrossing.InRectangle a b c d z})
  (hloX : lo 0 = a)
  (hhiX : hi 0 = a)
  (hstartX : estart 0 = a)
  (hloY : c ≤ lo 1)
  (hhiY : hi 1 ≤ d)
  (hescapeLeftBetween : ∀ z ∈ Set.range (eprefix.trans ((D.dualEmbedding.simpleWalkArc q).map D.dualEmbedding.coordinates.continuous)), z 0 = a → lo 1 < z 1 ∧ z 1 < hi 1)
  (hPrefixLower : Disjoint (Set.range eprefix) (Set.range lower))
  (hPrefixCore : Disjoint (Set.range eprefix) (Set.range ((D.primalEmbedding.simpleWalkArc p).map D.primalEmbedding.coordinates.continuous)))
  (hPrefixUpper : Disjoint (Set.range eprefix) (Set.range upper))
  (hCoreLower : Disjoint (Set.range ((D.dualEmbedding.simpleWalkArc q).map D.dualEmbedding.coordinates.continuous)) (Set.range lower))
  (hCoreUpper : Disjoint (Set.range ((D.dualEmbedding.simpleWalkArc q).map D.dualEmbedding.coordinates.continuous)) (Set.range upper))
  (hexit : D.dualEmbedding.vertexCoord t 0 = b ∨ (D.dualEmbedding.vertexCoord t 1 = d ∧ a < D.dualEmbedding.vertexCoord t 0 ∧ ∀ u : unitInterval, (lower.trans (((D.primalEmbedding.simpleWalkArc p).map D.primalEmbedding.coordinates.continuous).trans upper)) u 1 < d) ∨ (D.dualEmbedding.vertexCoord t 1 = c ∧ a < D.dualEmbedding.vertexCoord t 0 ∧ ∀ u : unitInterval, c < (lower.trans (((D.primalEmbedding.simpleWalkArc p).map D.primalEmbedding.coordinates.continuous).trans upper)) u 1)) :
-- imply
  False := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.no_open_dual_escape_of_doublyAttached_simpleCrosscut D omega p q hp hq hpopen hqopen hab hcd lower upper eprefix hcrossRect hescapeRect hloX hhiX hstartX hloY hhiY hescapeLeftBetween hPrefixLower hPrefixCore hPrefixUpper hCoreLower hCoreUpper hexit

/--
[no_open_dual_escape_of_doublyAttached_subpaths](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean)
-/
@[path]
private lemma no_open_dual_escape_of_doublyAttached_subpaths_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {D : PeriodicPlanarDualPair P Pdual}
  {omega : ConfigSpace (Sym2 V)}
  {x y : V}
  {s t : W}
  {p : P.graph.Walk x y}
  {q : Pdual.graph.Walk s t}
  {a b c d : Real}
  {lo px py hi estart eroot efinish : Fin 2 → Real}
  {lower : Path lo px}
  {pcore : Path px py}
  {upper : Path py hi}
  {eprefix : Path estart eroot}
  {ecore : Path eroot efinish}
-- given
  (hp : ¬ p.Nil)
  (hq : ¬ q.Nil)
  (hpopen : ∀ {u v : V}, s(u, v) ∈ p.edges → omega s(u, v) = true)
  (hqopen : ∀ {u v : W}, s(u, v) ∈ q.edges → dualConfigEquiv D.edgeDual omega s(u, v) = true)
  (hab : a < b)
  (hcd : c < d)
  (hpcoreRange : Set.range pcore ⊆ Set.range ((D.primalEmbedding.simpleWalkArc p).map D.primalEmbedding.coordinates.continuous))
  (hecoreRange : Set.range ecore ⊆ Set.range ((D.dualEmbedding.simpleWalkArc q).map D.dualEmbedding.coordinates.continuous))
  (hcrossRect : Set.range (lower.trans (pcore.trans upper)) ⊆ {z | ContinuousRectangleCrossing.InRectangle a b c d z})
  (hescapeRect : Set.range (eprefix.trans ecore) ⊆ {z | ContinuousRectangleCrossing.InRectangle a b c d z})
  (hloX : lo 0 = a)
  (hhiX : hi 0 = a)
  (hstartX : estart 0 = a)
  (hloY : c ≤ lo 1)
  (hhiY : hi 1 ≤ d)
  (hescapeLeftBetween : ∀ z ∈ Set.range (eprefix.trans ecore), z 0 = a → lo 1 < z 1 ∧ z 1 < hi 1)
  (hPrefixLower : Disjoint (Set.range eprefix) (Set.range lower))
  (hPrefixCore : Disjoint (Set.range eprefix) (Set.range pcore))
  (hPrefixUpper : Disjoint (Set.range eprefix) (Set.range upper))
  (hCoreLower : Disjoint (Set.range ecore) (Set.range lower))
  (hCoreUpper : Disjoint (Set.range ecore) (Set.range upper))
  (hexit : efinish 0 = b ∨ (efinish 1 = d ∧ a < efinish 0 ∧ ∀ u : unitInterval, (lower.trans (pcore.trans upper)) u 1 < d) ∨ (efinish 1 = c ∧ a < efinish 0 ∧ ∀ u : unitInterval, c < (lower.trans (pcore.trans upper)) u 1)) :
-- imply
  False := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.no_open_dual_escape_of_doublyAttached_subpaths D omega p q hp hq hpopen hqopen hab hcd lower pcore upper eprefix ecore hpcoreRange hecoreRange hcrossRect hescapeRect hloX hhiX hstartX hloY hhiY hescapeLeftBetween hPrefixLower hPrefixCore hPrefixUpper hCoreLower hCoreUpper hexit

/--
[complementaryDual_rightHalfPlane_measure_eq_zero_of_orderedJoinedBand_exclusion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean)
-/
@[path]
private lemma complementaryDual_rightHalfPlane_measure_eq_zero_of_orderedJoinedBand_exclusion_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {rPrimal rDual R : Real}
  {buffer : Nat}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hdualErgodic : Pdual.IsErgodic (D.dualMeasure mu))
  (hdualUnique : D.dualMeasure mu {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
  (hrR : rPrimal ≤ R)
  (hgeom : ∀ (n m : Nat) (L U : Finset V) (k : Nat), n + buffer < m → (L : Set V) ⊆ D.primalEmbedding.rightHalfPlaneVertices R → U = L.image (P.shift (verticalShift (1 + 2 * (m : Int)))) → (∀ x ∈ L, ∀ y ∈ U, D.primalEmbedding.vertexCoord x 1 + 2 * (n + buffer : Nat) + 2 < D.primalEmbedding.vertexCoord y 1) → Disjoint (D.primalEmbedding.finiteJoinedBoundaryArmEvent rPrimal (-(m : Real)) m k L U) ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.rightHalfPlaneBoundaryBandHasInfiniteCluster rDual (-(n : Real)) n)) :
-- imply
  D.dualMeasure mu (D.dualEmbedding.rightHalfPlaneHasInfiniteCluster rDual) = 0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.complementaryDual_rightHalfPlane_measure_eq_zero_of_orderedJoinedBand_exclusion D mu hFKG hTI hunique hdualErgodic hdualUnique rPrimal rDual R hrR buffer hgeom

/--
[complementaryDual_rightHalfPlane_measure_eq_zero_of_deepJoinedBand_exclusion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean)
-/
@[path]
private lemma complementaryDual_rightHalfPlane_measure_eq_zero_of_deepJoinedBand_exclusion_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {rPrimal rDual R : Real}
  {margin : Nat}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hdualErgodic : Pdual.IsErgodic (D.dualMeasure mu))
  (hdualUnique : D.dualMeasure mu {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
  (hrR : rPrimal ≤ R)
  (hmargin : 0 < margin)
  (hgeom : ∀ (n : Nat) (L U : Finset V) (k : Nat), (L : Set V) ⊆ D.primalEmbedding.rightHalfPlaneVertices R → U = L.image (P.shift (verticalShift (1 + 2 * (n + margin : Nat)))) → Disjoint (D.primalEmbedding.finiteJoinedBoundaryArmEvent rPrimal (-(n + margin : Nat) : Real) (n + margin : Nat) k L U) ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.rightHalfPlaneBoundaryBandHasInfiniteCluster rDual (-(n : Real)) n)) :
-- imply
  D.dualMeasure mu (D.dualEmbedding.rightHalfPlaneHasInfiniteCluster rDual) = 0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.complementaryDual_rightHalfPlane_measure_eq_zero_of_deepJoinedBand_exclusion D mu hFKG hTI hunique hdualErgodic hdualUnique rPrimal rDual R hrR margin hmargin hgeom

/--
[complementaryDual_rightHalfPlane_measure_eq_zero_of_joinedBand_exclusion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean)
-/
@[path]
private lemma complementaryDual_rightHalfPlane_measure_eq_zero_of_joinedBand_exclusion_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {rPrimal rDual : Real}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hdualErgodic : Pdual.IsErgodic (D.dualMeasure mu))
  (hdualUnique : D.dualMeasure mu {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
  (hgeom : ∀ (n : Nat) (L U : Finset V) (k : Nat), Disjoint (D.primalEmbedding.finiteJoinedBoundaryArmEvent rPrimal (-(n + 1 : Nat) : Real) (n + 1 : Nat) k L U) ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.rightHalfPlaneBoundaryBandHasInfiniteCluster rDual (-(n : Real)) n)) :
-- imply
  D.dualMeasure mu (D.dualEmbedding.rightHalfPlaneHasInfiniteCluster rDual) = 0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.complementaryDual_rightHalfPlane_measure_eq_zero_of_joinedBand_exclusion D mu hFKG hTI hunique hdualErgodic hdualUnique rPrimal rDual hgeom

/--
[PeriodicPlaneEmbedding.infiniteOpenBoundaryConnection_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean)
-/
@[path]
private lemma infiniteOpenBoundaryConnection_measurableSet_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {E : PeriodicPlaneEmbedding P}
  {r : Real}
  {S : Set V} :
-- imply
  MeasurableSet (E.infiniteOpenBoundaryConnection r S) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.infiniteOpenBoundaryConnection_measurableSet E r S

/--
[PeriodicPlaneEmbedding.infiniteOpenBoundaryConnection_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean)
-/
@[path]
private lemma infiniteOpenBoundaryConnection_isIncreasing_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {E : PeriodicPlaneEmbedding P}
  {r : Real}
  {S : Set V} :
-- imply
  IsIncreasing (E.infiniteOpenBoundaryConnection r S) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.infiniteOpenBoundaryConnection_isIncreasing E r S

/--
[PeriodicPlaneEmbedding.unique_two_sides_subset_infiniteOpenBoundaryConnection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean)
-/
@[path]
private lemma unique_two_sides_subset_infiniteOpenBoundaryConnection_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {E : PeriodicPlaneEmbedding P}
  {r : Real}
  {S T : Set V}
-- given
  (hS : S ⊆ E.rightHalfPlaneVertices r)
  (hT : T ⊆ (E.rightHalfPlaneVertices r)ᶜ) :
-- imply
  {omega : ConfigSpace (Sym2 V) | P.HasUniqueInfiniteCluster omega} ∩ (P.setHitsInfinite S ∩ P.setHitsInfinite T) ⊆ E.infiniteOpenBoundaryConnection r S := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.unique_two_sides_subset_infiniteOpenBoundaryConnection E r hS hT

/--
[PeriodicPlaneEmbedding.infiniteOpenBoundaryConnection_measureReal_ge_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean)
-/
@[path]
private lemma infiniteOpenBoundaryConnection_measureReal_ge_mul_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {r : Real}
  {S T : Set V}
-- given
  (hFKG : IsFKG mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hS : S ⊆ E.rightHalfPlaneVertices r)
  (hT : T ⊆ (E.rightHalfPlaneVertices r)ᶜ) :
-- imply
  mu.real (P.setHitsInfinite S) * mu.real (P.setHitsInfinite T) ≤ mu.real (E.infiniteOpenBoundaryConnection r S) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.infiniteOpenBoundaryConnection_measureReal_ge_mul E mu hFKG hunique r hS hT

/--
[PeriodicPlaneEmbedding.horizontalCrossingEvent_of_openWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean)
-/
@[path]
private lemma horizontalCrossingEvent_of_openWalk_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {E : PeriodicPlaneEmbedding P}
  {omega : ConfigSpace (Sym2 V)}
  {B a b c d : Real}
  {x y : V}
  {p : (P.openSubgraph omega).Walk x y}
-- given
  (hB : ∀ {u v : V} (huv : P.graph.Adj u v) (t) (i : Fin 2), |E.coordinates (E.edgeArc huv t - E.vertex u) i| ≤ B)
  (hB0 : 0 ≤ B)
  (hab : a + B < b)
  (hx : E.vertexCoord x 0 < a)
  (hy : b < E.vertexCoord y 0)
  (hpY : ∀ v ∈ p.support, c ≤ E.vertexCoord v 1 ∧ E.vertexCoord v 1 ≤ d) :
-- imply
  omega ∈ E.horizontalCrossingEvent a b c d := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.horizontalCrossingEvent_of_openWalk E omega hB hB0 hab p hx hy hpY

/--
[PeriodicPlaneEmbedding.verticalCrossingEvent_of_openWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean)
-/
@[path]
private lemma verticalCrossingEvent_of_openWalk_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {E : PeriodicPlaneEmbedding P}
  {omega : ConfigSpace (Sym2 V)}
  {B a b c d : Real}
  {x y : V}
  {p : (P.openSubgraph omega).Walk x y}
-- given
  (hB : ∀ {u v : V} (huv : P.graph.Adj u v) (t) (i : Fin 2), |E.coordinates (E.edgeArc huv t - E.vertex u) i| ≤ B)
  (hB0 : 0 ≤ B)
  (hcd : c + B < d)
  (hx : E.vertexCoord x 1 < c)
  (hy : d < E.vertexCoord y 1)
  (hpX : ∀ v ∈ p.support, a ≤ E.vertexCoord v 0 ∧ E.vertexCoord v 0 ≤ b) :
-- imply
  omega ∈ E.verticalCrossingEvent a b c d := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.verticalCrossingEvent_of_openWalk E omega hB hB0 hcd p hx hy hpX

/--
[PeriodicPlaneEmbedding.exists_open_rectExit_of_clusterWithinSet_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean)
-/
@[path]
private lemma exists_open_rectExit_of_clusterWithinSet_infinite_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {E : PeriodicPlaneEmbedding P}
  {omega : ConfigSpace (Sym2 V)}
  {A : Set V}
  {a b c d : Real}
  {x : V}
-- given
  (hxRect : x ∈ E.rectVertices a b c d)
  (hinfinite : (P.clusterWithinSet omega A x).Infinite) :
-- imply
  ∃ v ∈ E.rectVertices a b c d, ∃ z : V, (P.openSubgraph omega).Adj v z ∧ z ∉ E.rectVertices a b c d ∧ z ∈ A ∧ ∃ q : (P.openSubgraph omega).Walk x v, ∀ u ∈ q.support, u ∈ A ∩ E.rectVertices a b c d := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_open_rectExit_of_clusterWithinSet_infinite E omega A hxRect hinfinite

/--
[PeriodicPlaneEmbedding.exists_open_exposedRectExit_of_rightHalfPlane_cluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean)
-/
@[path]
private lemma exists_open_exposedRectExit_of_rightHalfPlane_cluster_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {E : PeriodicPlaneEmbedding P}
  {omega : ConfigSpace (Sym2 V)}
  {r b c d : Real}
  {x : V}
-- given
  (hxRect : x ∈ E.rectVertices r b c d)
  (hinfinite : (P.clusterWithinSet omega (E.rightHalfPlaneVertices r) x).Infinite) :
-- imply
  ∃ v ∈ E.rectVertices r b c d, ∃ z : V, (P.openSubgraph omega).Adj v z ∧ z ∈ E.rightHalfPlaneVertices r ∧ (b < E.vertexCoord z 0 ∨ E.vertexCoord z 1 < c ∨ d < E.vertexCoord z 1) ∧ ∃ q : (P.openSubgraph omega).Walk x v, ∀ u ∈ q.support, u ∈ E.rightHalfPlaneVertices r ∩ E.rectVertices r b c d := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_open_exposedRectExit_of_rightHalfPlane_cluster E omega hxRect hinfinite

/--
[not_infiniteComplementaryDualClusterWithin_rightHalfPlane_of_threeCrossings](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean)
-/
@[path]
private lemma not_infiniteComplementaryDualClusterWithin_rightHalfPlane_of_threeCrossings_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  [DecidableEq W]
  [Countable W]
  {D : PeriodicPlanarDualPair P Pdual}
  {omega : ConfigSpace (Sym2 V)}
  {B r R C D0 A Tbottom Ttop : Real}
  {x : W}
-- given
  (hBpos : 0 < B)
  (hBp : ∀ {u v : V} (huv : P.graph.Adj u v) (t) (i : Fin 2), |D.primalEmbedding.coordinates (D.primalEmbedding.edgeArc huv t - D.primalEmbedding.vertex u) i| ≤ B)
  (hBd : ∀ {u v : W} (huv : Pdual.graph.Adj u v) (t) (i : Fin 2), |D.dualEmbedding.coordinates (D.dualEmbedding.edgeArc huv t - D.dualEmbedding.vertex u) i| ≤ B)
  (hrR : r < R)
  (hRightWidth : A + 10 * B < R)
  (hBottom : C + 10 * B < Tbottom)
  (hTop : Ttop + 10 * B < D0)
  (hxRect : x ∈ D.dualEmbedding.rectVertices r R C D0)
  (hxRight : D.dualEmbedding.vertexCoord x 0 < A)
  (hxBottom : Tbottom < D.dualEmbedding.vertexCoord x 1)
  (hxTop : D.dualEmbedding.vertexCoord x 1 < Ttop)
  (hRightCrossing : omega ∈ D.primalEmbedding.verticalCrossingEvent (A + 4 * B) (R - 4 * B) (C - 4 * B) (D0 + 4 * B))
  (hBottomCrossing : omega ∈ D.primalEmbedding.horizontalCrossingEvent (r - 5 * B) (R + 5 * B) (C + 4 * B) (Tbottom - 4 * B))
  (hTopCrossing : omega ∈ D.primalEmbedding.horizontalCrossingEvent (r - 5 * B) (R + 5 * B) (Ttop + 4 * B) (D0 - 4 * B)) :
-- imply
  ¬(Pdual.clusterWithinSet (dualConfigEquiv D.edgeDual omega) (D.dualEmbedding.rightHalfPlaneVertices r) x).Infinite := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.not_infiniteComplementaryDualClusterWithin_rightHalfPlane_of_threeCrossings D omega hBpos hBp hBd hrR hRightWidth hBottom hTop hxRect hxRight hxBottom hxTop hRightCrossing hBottomCrossing hTopCrossing


-- created on 2026-10-23
