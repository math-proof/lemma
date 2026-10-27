import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPreferenceClosure
open Set SimpleGraph StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[exists_common_preference_grid_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceClosure.lean)
-/
@[path]
private lemma exists_common_preference_grid_witness_eq
  {n m : Nat}
  {bottomColor topColor : Bool}
-- given
  (hn : 0 < n)
  (vertical horizontal : PreferenceGridVertex n m -> Bool)
  (hbottom : forall i : Fin (n + 1), vertical (i, 0) = bottomColor)
  (htop : forall i : Fin (n + 1), vertical (i, Fin.last m) = topColor)
  (hverticalEnds : bottomColor ≠ topColor)
  (hleft : forall j : Fin (m + 1), horizontal (0, j) = true)
  (hright : forall j : Fin (m + 1), horizontal (Fin.last n, j) = false) :
-- imply
  exists x : PreferenceGridVertex n m, vertical x = true /\ horizontal x = true /\ (exists xVertical : PreferenceGridVertex n m, KingAdj (preferenceGridSite x) (preferenceGridSite xVertical) /\ vertical xVertical = false) /\ (exists xHorizontal : PreferenceGridVertex n m, KingAdj (preferenceGridSite x) (preferenceGridSite xHorizontal) /\ horizontal xHorizontal = false) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.exists_common_preference_grid_witness hn vertical horizontal bottomColor topColor hbottom htop hverticalEnds hleft hright


-- created on 2026-10-23
