import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldDeepConnectorRows.Part2
open Filter MeasureTheory Set StatMech StatMech.FK StatMech.FK.PeriodicPlanar StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair


/--
[PeriodicPlaneEmbedding.exists_separated_finiteDeepOpenExitedJoinedBoundaryArmEvent_measureReal_gt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldDeepConnectorRows.lean)
-/
@[path]
private lemma exists_separated_finiteDeepOpenExitedJoinedBoundaryArmEvent_measureReal_gt_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {r R : Real}
  {s : Real}
  {t : Int}
  {N : Nat}
  {epsilon : Real}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hrR : r ≤ R)
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ L U : Finset V, ∃ width : Nat, (L : Set V) ⊆ E.rightHalfPlaneVertices R ∧ (U : Set V) ⊆ E.rightHalfPlaneVertices R ∧ U = L.image (P.shift (verticalShift (1 + t))) ∧ 1 - 2 * Real.sqrt (1 - (mu.real (P.orbitBoxHitsInfinite N)) ^ 2) - 3 * epsilon < mu.real (E.finiteDeepOpenExitedJoinedBoundaryArmEvent r R s (s + t) width L U) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_separated_finiteDeepOpenExitedJoinedBoundaryArmEvent_measureReal_gt E mu hFKG hTI hunique hrR s t N hepsilon

/--
[complementaryDual_rightHalfPlane_measure_eq_zero_of_separatedRows](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldDeepConnectorRows.lean)
-/
@[path]
private lemma complementaryDual_rightHalfPlane_measure_eq_zero_of_separatedRows_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {rDual : Real}
  {r R : Real}
  {s : Nat → Real}
  {t : Nat → Int}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hdualErgodic : Pdual.IsErgodic (D.dualMeasure mu))
  (hdualUnique : D.dualMeasure mu {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
  (hrR : r ≤ R)
  (hdisjoint : ∀ (band : Nat) (L U : Finset V) (width : Nat), (L : Set V) ⊆ D.primalEmbedding.rightHalfPlaneVertices R → (U : Set V) ⊆ D.primalEmbedding.rightHalfPlaneVertices R → U = L.image (P.shift (verticalShift (1 + t band))) → Disjoint (D.primalEmbedding.finiteDeepOpenExitedJoinedBoundaryArmEvent r R (s band) (s band + t band) width L U) ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.rightHalfPlaneBoundaryBandHasInfiniteCluster rDual (-(band : Real)) band)) :
-- imply
  D.dualMeasure mu (D.dualEmbedding.rightHalfPlaneHasInfiniteCluster rDual) = 0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.complementaryDual_rightHalfPlane_measure_eq_zero_of_separatedRows D mu hFKG hTI hunique hdualErgodic hdualUnique rDual hrR s t hdisjoint


-- created on 2026-10-23
