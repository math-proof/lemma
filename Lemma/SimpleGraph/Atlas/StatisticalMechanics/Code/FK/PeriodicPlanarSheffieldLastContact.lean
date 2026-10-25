import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldLastContact
open Set StatMech StatMech.FK StatMech.FK.PeriodicPlanar StatMech.FK.PeriodicPlanar.ContinuousHalfPlaneCrosscut


/--
[exists_first_line_contact_prefix_in_halfPlane](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldLastContact.lean)
-/
@[path]
private lemma exists_first_line_contact_prefix_in_halfPlane_eq
  {start finish : Fin 2 -> Real}
  {gamma : Path start finish}
  {i : Fin 2}
  {a : Real}
-- given
  (hstart : start i <= a)
  (hfinish : a <= finish i) :
-- imply
  exists t : unitInterval, gamma t i = a /\ (forall u : unitInterval, gamma u i = a -> t <= u) /\ Set.range (gamma.subpath 0 t) <= Set.range gamma /\ forall z : Fin 2 -> Real, z ∈ Set.range (gamma.subpath 0 t) -> z i <= a := by
-- proof
  apply StatMech.FK.PeriodicPlanar.ContinuousHalfPlaneCrosscut.exists_first_line_contact_prefix_in_halfPlane gamma i a hstart hfinish

/--
[exists_last_line_contact_suffix_in_halfPlane](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldLastContact.lean)
-/
@[path]
private lemma exists_last_line_contact_suffix_in_halfPlane_eq
  {start finish : Fin 2 -> Real}
  {gamma : Path start finish}
  {i : Fin 2}
  {a : Real}
-- given
  (hstart : start i <= a)
  (hfinish : a <= finish i) :
-- imply
  exists t : unitInterval, gamma t i = a /\ (forall u : unitInterval, gamma u i = a -> u <= t) /\ Set.range (gamma.subpath t 1) <= Set.range gamma /\ forall z : Fin 2 -> Real, z ∈ Set.range (gamma.subpath t 1) -> a <= z i := by
-- proof
  apply StatMech.FK.PeriodicPlanar.ContinuousHalfPlaneCrosscut.exists_last_line_contact_suffix_in_halfPlane gamma i a hstart hfinish

/--
[exists_first_line_contact_prefix_in_upperHalfPlane](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldLastContact.lean)
-/
@[path]
private lemma exists_first_line_contact_prefix_in_upperHalfPlane_eq
  {start finish : Fin 2 -> Real}
  {gamma : Path start finish}
  {i : Fin 2}
  {a : Real}
-- given
  (hstart : a <= start i)
  (hfinish : finish i <= a) :
-- imply
  exists t : unitInterval, gamma t i = a /\ (forall u : unitInterval, gamma u i = a -> t <= u) /\ Set.range (gamma.subpath 0 t) <= Set.range gamma /\ forall z : Fin 2 -> Real, z ∈ Set.range (gamma.subpath 0 t) -> a <= z i := by
-- proof
  apply StatMech.FK.PeriodicPlanar.ContinuousHalfPlaneCrosscut.exists_first_line_contact_prefix_in_upperHalfPlane gamma i a hstart hfinish

/--
[exists_last_line_contact_suffix_in_lowerHalfPlane](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldLastContact.lean)
-/
@[path]
private lemma exists_last_line_contact_suffix_in_lowerHalfPlane_eq
  {start finish : Fin 2 -> Real}
  {gamma : Path start finish}
  {i : Fin 2}
  {a : Real}
-- given
  (hstart : a <= start i)
  (hfinish : finish i <= a) :
-- imply
  exists t : unitInterval, gamma t i = a /\ (forall u : unitInterval, gamma u i = a -> u <= t) /\ Set.range (gamma.subpath t 1) <= Set.range gamma /\ forall z : Fin 2 -> Real, z ∈ Set.range (gamma.subpath t 1) -> z i <= a := by
-- proof
  apply StatMech.FK.PeriodicPlanar.ContinuousHalfPlaneCrosscut.exists_last_line_contact_suffix_in_lowerHalfPlane gamma i a hstart hfinish

/--
[exists_upper_line_excursion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldLastContact.lean)
-/
@[path]
private lemma exists_upper_line_excursion_eq
  {start finish : Fin 2 -> Real}
  {gamma : Path start finish}
  {i : Fin 2}
  {a : Real}
  {t : unitInterval}
-- given
  (hstart : start i <= a)
  (hfinish : finish i <= a)
  (ht : a <= gamma t i) :
-- imply
  (∃ (lo hi : Fin 2 -> Real) (lower : Path lo (gamma t)) (upper : Path (gamma t) hi), lo i = a /\ hi i = a /\ Set.range lower <= Set.range gamma /\ Set.range upper <= Set.range gamma /\ (forall z : Fin 2 -> Real, z ∈ Set.range lower -> a <= z i) /\ (forall z : Fin 2 -> Real, z ∈ Set.range upper -> a <= z i)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.ContinuousHalfPlaneCrosscut.exists_upper_line_excursion gamma i a hstart hfinish t ht

/--
[exists_lower_line_excursion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldLastContact.lean)
-/
@[path]
private lemma exists_lower_line_excursion_eq
  {start finish : Fin 2 -> Real}
  {gamma : Path start finish}
  {i : Fin 2}
  {a : Real}
  {t : unitInterval}
-- given
  (hstart : a <= start i)
  (hfinish : a <= finish i)
  (ht : gamma t i <= a) :
-- imply
  (∃ (lo hi : Fin 2 -> Real) (lower : Path lo (gamma t)) (upper : Path (gamma t) hi), lo i = a /\ hi i = a /\ Set.range lower <= Set.range gamma /\ Set.range upper <= Set.range gamma /\ (forall z : Fin 2 -> Real, z ∈ Set.range lower -> z i <= a) /\ (forall z : Fin 2 -> Real, z ∈ Set.range upper -> z i <= a)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.ContinuousHalfPlaneCrosscut.exists_lower_line_excursion gamma i a hstart hfinish t ht

/--
[exists_upper_line_excursion_path](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldLastContact.lean)
-/
@[path]
private lemma exists_upper_line_excursion_path_eq
  {start finish : Fin 2 -> Real}
  {gamma : Path start finish}
  {i : Fin 2}
  {a : Real}
  {t : unitInterval}
-- given
  (hstart : start i <= a)
  (hfinish : finish i <= a)
  (ht : a <= gamma t i) :
-- imply
  ∃ (lo hi : Fin 2 -> Real) (excursion : Path lo hi), lo i = a /\ hi i = a /\ Set.range excursion <= Set.range gamma /\ ∀ z : Fin 2 -> Real, z ∈ Set.range excursion -> a <= z i := by
-- proof
  apply StatMech.FK.PeriodicPlanar.ContinuousHalfPlaneCrosscut.exists_upper_line_excursion_path gamma i a hstart hfinish t ht

/--
[exists_lower_line_excursion_path](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldLastContact.lean)
-/
@[path]
private lemma exists_lower_line_excursion_path_eq
  {start finish : Fin 2 -> Real}
  {gamma : Path start finish}
  {i : Fin 2}
  {a : Real}
  {t : unitInterval}
-- given
  (hstart : a <= start i)
  (hfinish : a <= finish i)
  (ht : gamma t i <= a) :
-- imply
  ∃ (lo hi : Fin 2 -> Real) (excursion : Path lo hi), lo i = a /\ hi i = a /\ Set.range excursion <= Set.range gamma /\ ∀ z : Fin 2 -> Real, z ∈ Set.range excursion -> z i <= a := by
-- proof
  apply StatMech.FK.PeriodicPlanar.ContinuousHalfPlaneCrosscut.exists_lower_line_excursion_path gamma i a hstart hfinish t ht


-- created on 2026-10-23
