import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldOpenBoundaryCorridor
open Filter MeasureTheory Set StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[PeriodicPlaneEmbedding.infiniteOpenBoundaryConnectionTo_boundary_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldOpenBoundaryCorridor.lean)
-/
@[path]
private lemma infiniteOpenBoundaryConnectionTo_boundary_eq_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {r : Real}
  {S : Set V} :
-- imply
  E.infiniteOpenBoundaryConnectionTo r S (E.rightHalfPlaneBoundaryVertices r) = E.infiniteOpenBoundaryConnection r S := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.infiniteOpenBoundaryConnectionTo_boundary_eq E r S

/--
[PeriodicPlaneEmbedding.infiniteOpenLowerBoundaryConnection_mono_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldOpenBoundaryCorridor.lean)
-/
@[path]
private lemma infiniteOpenLowerBoundaryConnection_mono_add_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {r s : Real}
  {S : Set V} :
-- imply
  Monotone (fun n : Nat => E.infiniteOpenBoundaryConnectionTo r S (E.lowerBoundaryRayVertices r (s + n))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.infiniteOpenLowerBoundaryConnection_mono_add E r s S

/--
[PeriodicPlaneEmbedding.iUnion_infiniteOpenLowerBoundaryConnection_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldOpenBoundaryCorridor.lean)
-/
@[path]
private lemma iUnion_infiniteOpenLowerBoundaryConnection_add_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {r s : Real}
  {S : Set V} :
-- imply
  (⋃ n : Nat, E.infiniteOpenBoundaryConnectionTo r S (E.lowerBoundaryRayVertices r (s + n))) = E.infiniteOpenBoundaryConnection r S := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.iUnion_infiniteOpenLowerBoundaryConnection_add E r s S

/--
[PeriodicPlaneEmbedding.infiniteOpenLowerBoundaryConnection_tendsto_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldOpenBoundaryCorridor.lean)
-/
@[path]
private lemma infiniteOpenLowerBoundaryConnection_tendsto_add_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsFiniteMeasure mu]
  {r s : Real}
  {S : Set V} :
-- imply
  Tendsto (fun n : Nat => mu.real (E.infiniteOpenBoundaryConnectionTo r S (E.lowerBoundaryRayVertices r (s + n)))) atTop (nhds (mu.real (E.infiniteOpenBoundaryConnection r S))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.infiniteOpenLowerBoundaryConnection_tendsto_add E mu r s S

/--
[PeriodicPlaneEmbedding.infiniteOpenUpperBoundaryConnection_mono_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldOpenBoundaryCorridor.lean)
-/
@[path]
private lemma infiniteOpenUpperBoundaryConnection_mono_sub_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {r s : Real}
  {S : Set V} :
-- imply
  Monotone (fun n : Nat => E.infiniteOpenBoundaryConnectionTo r S (E.upperBoundaryRayVertices r (s - n))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.infiniteOpenUpperBoundaryConnection_mono_sub E r s S

/--
[PeriodicPlaneEmbedding.iUnion_infiniteOpenUpperBoundaryConnection_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldOpenBoundaryCorridor.lean)
-/
@[path]
private lemma iUnion_infiniteOpenUpperBoundaryConnection_sub_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {r s : Real}
  {S : Set V} :
-- imply
  (⋃ n : Nat, E.infiniteOpenBoundaryConnectionTo r S (E.upperBoundaryRayVertices r (s - n))) = E.infiniteOpenBoundaryConnection r S := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.iUnion_infiniteOpenUpperBoundaryConnection_sub E r s S

/--
[PeriodicPlaneEmbedding.infiniteOpenUpperBoundaryConnection_tendsto_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldOpenBoundaryCorridor.lean)
-/
@[path]
private lemma infiniteOpenUpperBoundaryConnection_tendsto_sub_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsFiniteMeasure mu]
  {r s : Real}
  {S : Set V} :
-- imply
  Tendsto (fun n : Nat => mu.real (E.infiniteOpenBoundaryConnectionTo r S (E.upperBoundaryRayVertices r (s - n)))) atTop (nhds (mu.real (E.infiniteOpenBoundaryConnection r S))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.infiniteOpenUpperBoundaryConnection_tendsto_sub E mu r s S

/--
[PeriodicPlaneEmbedding.infiniteOpenBoundaryConnection_measureReal_vertical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldOpenBoundaryCorridor.lean)
-/
@[path]
private lemma infiniteOpenBoundaryConnection_measureReal_vertical_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {t : Int}
  {r : Real}
  {S : Set V}
-- given
  (hTI : P.IsTranslationInvariant mu) :
-- imply
  mu.real (E.infiniteOpenBoundaryConnection r (P.shift (verticalShift t) '' S)) = mu.real (E.infiniteOpenBoundaryConnection r S) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.infiniteOpenBoundaryConnection_measureReal_vertical E mu hTI t r S

/--
[PeriodicPlaneEmbedding.shift_down_infiniteOpenLowerBoundary_tendsto_at](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldOpenBoundaryCorridor.lean)
-/
@[path]
private lemma shift_down_infiniteOpenLowerBoundary_tendsto_at_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsFiniteMeasure mu]
  {r s : Real}
  {S : Set V}
-- given
  (hTI : P.IsTranslationInvariant mu) :
-- imply
  Tendsto (fun n : Nat => mu.real (E.infiniteOpenBoundaryConnectionTo r (P.shift (verticalShift (-(n : Int))) '' S) (E.lowerBoundaryRayVertices r s))) atTop (nhds (mu.real (E.infiniteOpenBoundaryConnection r S))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.shift_down_infiniteOpenLowerBoundary_tendsto_at E mu hTI r s S

/--
[PeriodicPlaneEmbedding.shift_up_infiniteOpenUpperBoundary_tendsto_at](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldOpenBoundaryCorridor.lean)
-/
@[path]
private lemma shift_up_infiniteOpenUpperBoundary_tendsto_at_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsFiniteMeasure mu]
  {r s : Real}
  {S : Set V}
-- given
  (hTI : P.IsTranslationInvariant mu) :
-- imply
  Tendsto (fun n : Nat => mu.real (E.infiniteOpenBoundaryConnectionTo r (P.shift (verticalShift (n : Int)) '' S) (E.upperBoundaryRayVertices r s))) atTop (nhds (mu.real (E.infiniteOpenBoundaryConnection r S))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.shift_up_infiniteOpenUpperBoundary_tendsto_at E mu hTI r s S

/--
[PeriodicPlaneEmbedding.exists_finite_infiniteOpenBoundaryConnection_gt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldOpenBoundaryCorridor.lean)
-/
@[path]
private lemma exists_finite_infiniteOpenBoundaryConnection_gt_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {r R : Real}
  {epsilon : Real}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hrR : r ≤ R)
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ S : Finset V, (S : Set V) ⊆ E.rightHalfPlaneVertices R ∧ 1 - epsilon < mu.real (E.infiniteOpenBoundaryConnection r (S : Set V)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_finite_infiniteOpenBoundaryConnection_gt E mu hFKG hTI hunique hrR hepsilon

/--
[PeriodicPlaneEmbedding.exists_finite_opposite_infiniteOpenBoundaryRays_gt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldOpenBoundaryCorridor.lean)
-/
@[path]
private lemma exists_finite_opposite_infiniteOpenBoundaryRays_gt_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {r R c d : Real}
  {epsilon : Real}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hrR : r ≤ R)
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ L U : Finset V, (L : Set V) ⊆ E.rightHalfPlaneVertices R ∧ (U : Set V) ⊆ E.rightHalfPlaneVertices R ∧ 1 - epsilon < mu.real (E.infiniteOpenBoundaryConnectionTo r (L : Set V) (E.lowerBoundaryRayVertices r c)) ∧ 1 - epsilon < mu.real (E.infiniteOpenBoundaryConnectionTo r (U : Set V) (E.upperBoundaryRayVertices r d)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_finite_opposite_infiniteOpenBoundaryRays_gt E mu hFKG hTI hunique hrR hepsilon


-- created on 2026-10-23
