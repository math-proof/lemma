import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSplitPhase.Part3
open StatMech StatMech.FrontierA


/--
[triangularTorusSplitEmbedHom_mapDart_direction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitPhase.lean)
-/
@[path]
private lemma triangularTorusSplitEmbedHom_mapDart_direction_eq
  {L : Nat}
  [Fact (2 < L)]
  {d : (kwOrderedDartPortSplitGraph (triangularTorusGraph L) (triangularTorusLocalPortOrder L)).Dart} :
-- imply
  triangularTorusGraphDartDirection (3 * L) ((triangularTorusSplitEmbedHom L).mapDart d) = triangularTorusSplitDartDirection L d := by
-- proof
  apply StatMech.FrontierA.triangularTorusSplitEmbedHom_mapDart_direction L d

/--
[triangularSplit_entry_phase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitPhase.lean)
-/
@[path]
private lemma triangularSplit_entry_phase_eq
  {rho : Complex}
  {a b : Fin 6}
-- given
  (hrho : rho ^ 4 = Complex.I)
  (hadj : (triangularTorusDirectionRank a).val + 1 = (triangularTorusDirectionRank b).val ∨ (triangularTorusDirectionRank b).val + 1 = (triangularTorusDirectionRank a).val) :
-- imply
  triangularKacWardTurnMatrix rho (triangularTorusDirectionReverse a) (triangularTorusSplitInternalDirection a b) = (if (triangularTorusDirectionRank a).val < (triangularTorusDirectionRank b).val then -Complex.I * (rho ^ triangularTorusDirectionSignedAngle a)⁻¹ else Complex.I * (rho ^ triangularTorusDirectionSignedAngle a)⁻¹) * triangularTorusSplitInternalGauge rho a b := by
-- proof
  apply StatMech.FrontierA.triangularSplit_entry_phase rho hrho a b hadj

/--
[triangularSplit_exit_phase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitPhase.lean)
-/
@[path]
private lemma triangularSplit_exit_phase_eq
  {rho : Complex}
  {a b : Fin 6}
-- given
  (hrho : rho ^ 4 = Complex.I)
  (hadj : (triangularTorusDirectionRank a).val + 1 = (triangularTorusDirectionRank b).val ∨ (triangularTorusDirectionRank b).val + 1 = (triangularTorusDirectionRank a).val) :
-- imply
  triangularKacWardTurnMatrix rho (triangularTorusSplitInternalDirection a b) b = (triangularTorusSplitInternalGauge rho a b)⁻¹ * rho ^ triangularTorusDirectionSignedAngle b := by
-- proof
  apply StatMech.FrontierA.triangularSplit_exit_phase rho hrho a b hadj

/--
[triangularSplit_internal_phase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitPhase.lean)
-/
@[path]
private lemma triangularSplit_internal_phase_eq
  {rho : Complex}
  {a b c : Fin 6}
-- given
  (hrho : rho ^ 4 = Complex.I)
  (hab : (triangularTorusDirectionRank a).val + 1 = (triangularTorusDirectionRank b).val ∨ (triangularTorusDirectionRank b).val + 1 = (triangularTorusDirectionRank a).val)
  (hbc : (triangularTorusDirectionRank b).val + 1 = (triangularTorusDirectionRank c).val ∨ (triangularTorusDirectionRank c).val + 1 = (triangularTorusDirectionRank b).val)
  (hmono : ((triangularTorusDirectionRank a).val < (triangularTorusDirectionRank b).val ∧ (triangularTorusDirectionRank b).val < (triangularTorusDirectionRank c).val) ∨ ((triangularTorusDirectionRank b).val < (triangularTorusDirectionRank a).val ∧ (triangularTorusDirectionRank c).val < (triangularTorusDirectionRank b).val)) :
-- imply
  triangularKacWardTurnMatrix rho (triangularTorusSplitInternalDirection a b) (triangularTorusSplitInternalDirection b c) = (triangularTorusSplitInternalGauge rho a b)⁻¹ * triangularTorusSplitInternalGauge rho b c := by
-- proof
  apply StatMech.FrontierA.triangularSplit_internal_phase rho hrho a b c hab hbc hmono

/--
[triangularTorusSplitPhaseGauge_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitPhase.lean)
-/
@[path]
private lemma triangularTorusSplitPhaseGauge_ne_zero_eq
  {L : Nat}
  [Fact (2 < L)]
  {rho : Complex}
  {d : (kwOrderedDartPortSplitGraph (triangularTorusGraph L) (triangularTorusLocalPortOrder L)).Dart}
-- given
  (hrho : rho ^ 4 = Complex.I) :
-- imply
  triangularTorusSplitPhaseGauge L rho d ≠ 0 := by
-- proof
  apply StatMech.FrontierA.triangularTorusSplitPhaseGauge_ne_zero L rho hrho d

/--
[triangularTorusSplit_embedPhase_eq_phaseGauge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitPhase.lean)
-/
@[path]
private lemma triangularTorusSplit_embedPhase_eq_phaseGauge_eq
  {L : Nat}
  [Fact (2 < L)]
  {rho : Complex}
  {d e : (kwOrderedDartPortSplitGraph (triangularTorusGraph L) (triangularTorusLocalPortOrder L)).Dart}
-- given
  (hrho : rho ^ 4 = Complex.I)
  (hconnect : d.snd = e.fst)
  (hne : d.edge ≠ e.edge) :
-- imply
  triangularTorusGraphPhase (3 * L) rho 1 1 ((triangularTorusSplitEmbedHom L).mapDart d) ((triangularTorusSplitEmbedHom L).mapDart e) = kwPhaseGauge (triangularTorusSplitPhaseGauge L rho) (kwLocalAngularSplitPhase (triangularTorusLocalAngularData L rho hrho)) d e := by
-- proof
  apply StatMech.FrontierA.triangularTorusSplit_embedPhase_eq_phaseGauge L rho hrho d e hconnect hne


-- created on 2026-10-23
