import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneExclusion.Part2
open MeasureTheory Set SimpleGraph StatMech StatMech.FK StatMech.FK.PeriodicPlanar StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair


/--
[PeriodicPlaneEmbedding.primalHalfPlaneBarrierReady_measureReal_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneExclusion.lean)
-/
@[path]
private lemma primalHalfPlaneBarrierReady_measureReal_eq_one_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1) :
-- imply
  mu.real E.primalHalfPlaneBarrierReady = 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.primalHalfPlaneBarrierReady_measureReal_eq_one E mu hFKG hTI hunique

/--
[not_primalBarrierReady_and_complementaryDualTransverseWalks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneExclusion.lean)
-/
@[path]
private lemma not_primalBarrierReady_and_complementaryDualTransverseWalks_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {D : PeriodicPlanarDualPair P Pdual}
  {omega : ConfigSpace (Sym2 V)} :
-- imply
  ¬(D.primalEmbedding.primalHalfPlaneBarrierReady omega ∧ D.HasOpenComplementaryDualTransverseWalks omega) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.not_primalBarrierReady_and_complementaryDualTransverseWalks D omega


-- created on 2026-10-23
