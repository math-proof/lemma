import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalExternal.Part3
open StatMech StatMech.Onsager


/--
[ons_decFormalLogCoeff_eq_rooted_add_avoid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalExternal.lean)
-/
@[path]
private lemma ons_decFormalLogCoeff_eq_rooted_add_avoid_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {d : ons_Dart L}
  {m : ons_DecEdge L →₀ ℕ} :
-- imply
  ons_decFormalLogCoeff L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b) m = ons_decFormalRootedLogCoeff L a b d m + ons_decFormalAvoidLogCoeff L a b d m := by
-- proof
  apply StatMech.Onsager.ons_decFormalLogCoeff_eq_rooted_add_avoid L a b d m

/--
[ons_decFormalLog_eq_rooted_add_avoid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalExternal.lean)
-/
@[path]
private lemma ons_decFormalLog_eq_rooted_add_avoid_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {d : ons_Dart L} :
-- imply
  ons_decFormalLog L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b) = ons_decFormalRootedLog L a b d + ons_decFormalAvoidLog L a b d := by
-- proof
  apply StatMech.Onsager.ons_decFormalLog_eq_rooted_add_avoid L a b d

/--
[ons_decFormalFixedBucketN_eq_zero_of_external](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalExternal.lean)
-/
@[path]
private lemma ons_decFormalFixedBucketN_eq_zero_of_external_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {d : ons_Dart L}
  {r : ℕ}
  {m : ons_DecEdge L →₀ ℕ}
-- given
  (hmedge : m s(d, ons_dartRev L d) ≠ 0) :
-- imply
  ons_decFormalFixedBucketN L a b d r m = 0 := by
-- proof
  apply StatMech.Onsager.ons_decFormalFixedBucketN_eq_zero_of_external L a b d r m hmedge

/--
[ons_decFormalAvoidLogCoeff_eq_zero_of_external](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalExternal.lean)
-/
@[path]
private lemma ons_decFormalAvoidLogCoeff_eq_zero_of_external_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {d : ons_Dart L}
  {m : ons_DecEdge L →₀ ℕ}
-- given
  (hmedge : m s(d, ons_dartRev L d) ≠ 0) :
-- imply
  ons_decFormalAvoidLogCoeff L a b d m = 0 := by
-- proof
  apply StatMech.Onsager.ons_decFormalAvoidLogCoeff_eq_zero_of_external L a b d m hmedge

/--
[ons_decFormalAvoidLog_constantCoeff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalExternal.lean)
-/
@[path]
private lemma ons_decFormalAvoidLog_constantCoeff_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {d : ons_Dart L} :
-- imply
  MvPowerSeries.constantCoeff (ons_decFormalAvoidLog L a b d) = 0 := by
-- proof
  apply StatMech.Onsager.ons_decFormalAvoidLog_constantCoeff L a b d

/--
[ons_decFormalAvoidLog_hasSubst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalExternal.lean)
-/
@[path]
private lemma ons_decFormalAvoidLog_hasSubst_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {d : ons_Dart L} :
-- imply
  PowerSeries.HasSubst (ons_decFormalAvoidLog L a b d) := by
-- proof
  apply StatMech.Onsager.ons_decFormalAvoidLog_hasSubst L a b d

/--
[ons_decFormalAvoidRoot_coeff_eq_zero_of_external](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalExternal.lean)
-/
@[path]
private lemma ons_decFormalAvoidRoot_coeff_eq_zero_of_external_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {d : ons_Dart L}
  {m : ons_DecEdge L →₀ ℕ}
-- given
  (hmedge : m s(d, ons_dartRev L d) ≠ 0) :
-- imply
  MvPowerSeries.coeff m (ons_decFormalAvoidRoot L a b d) = 0 := by
-- proof
  apply StatMech.Onsager.ons_decFormalAvoidRoot_coeff_eq_zero_of_external L a b d m hmedge

/--
[ons_decLoopExponent_external_eq_one_of_firstReturn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalExternal.lean)
-/
@[path]
private lemma ons_decLoopExponent_external_eq_one_of_firstReturn_eq
  {L : ℕ}
  [Fact (2 < L)]
  {n : ℕ}
  [NeZero n]
  {d : ons_Dart L}
  {loop : Fin n → ons_Dart L}
-- given
  (hfirst : ons_decIsFirstReturnLoop d loop) :
-- imply
  ons_decLoopExponent L loop s(d, ons_dartRev L d) = 1 := by
-- proof
  apply StatMech.Onsager.ons_decLoopExponent_external_eq_one_of_firstReturn L d loop hfirst

/--
[ons_decFormalFirstReturnCoeff_eq_zero_unless_external_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalExternal.lean)
-/
@[path]
private lemma ons_decFormalFirstReturnCoeff_eq_zero_unless_external_one_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {d : ons_Dart L}
  {m : ons_DecEdge L →₀ ℕ}
-- given
  (hmedge : m s(d, ons_dartRev L d) ≠ 1) :
-- imply
  ons_decFormalFirstReturnCoeff L a b d m = 0 := by
-- proof
  apply StatMech.Onsager.ons_decFormalFirstReturnCoeff_eq_zero_unless_external_one L a b d m hmedge

/--
[ons_decFormalFirstReturn_constantCoeff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalExternal.lean)
-/
@[path]
private lemma ons_decFormalFirstReturn_constantCoeff_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {d : ons_Dart L} :
-- imply
  MvPowerSeries.constantCoeff (ons_decFormalFirstReturn L a b d) = 0 := by
-- proof
  apply StatMech.Onsager.ons_decFormalFirstReturn_constantCoeff L a b d

/--
[ons_decFormalFirstReturn_hasSubst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalExternal.lean)
-/
@[path]
private lemma ons_decFormalFirstReturn_hasSubst_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {d : ons_Dart L} :
-- imply
  PowerSeries.HasSubst (ons_decFormalFirstReturn L a b d) := by
-- proof
  apply StatMech.Onsager.ons_decFormalFirstReturn_hasSubst L a b d


-- created on 2026-10-23
