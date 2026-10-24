import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldDualBoundaryBands
open Filter MeasureTheory Set Topology StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[exists_pairedAlignedMarginSchedule](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldDualBoundaryBands.lean)
-/
@[path]
private lemma exists_pairedAlignedMarginSchedule_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {muDual : Measure (ConfigSpace (Sym2 W))}
  {S : Finset V}
  {Sdual : Finset W}
  {p pDual : Real}
  {family : E.NormalBoundaryBandFamily mu S p}
  {familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual}
-- given
  (verticalRequirement horizontalRequirement : Nat → Nat) :
-- imply
  Nonempty (PairedAlignedMarginSchedule E Edual family familyDual verticalRequirement horizontalRequirement) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.exists_pairedAlignedMarginSchedule E Edual family familyDual verticalRequirement horizontalRequirement

/--
[exists_pairedMixedGridDimensions](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldDualBoundaryBands.lean)
-/
@[path]
private lemma exists_pairedMixedGridDimensions_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {muDual : Measure (ConfigSpace (Sym2 W))}
  {S : Finset V}
  {Sdual : Finset W}
  {p pDual : Real}
  {family : E.NormalBoundaryBandFamily mu S p}
  {familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual}
-- given
  (horizontalMargin verticalMargin minimumX minimumY : Nat) :
-- imply
  ∃ extentX extentY width height widthDual heightDual : Nat, minimumX ≤ extentX ∧ minimumY ≤ extentY ∧ 0 < width ∧ 0 < height ∧ 0 < widthDual ∧ 0 < heightDual ∧ (family.baseLeft 0 + horizontalMargin + width - (family.baseRight 0 - horizontalMargin) : Int) = extentX ∧ (familyDual.baseLeft 0 + horizontalMargin + widthDual - (familyDual.baseRight 0 - horizontalMargin) : Int) = extentX ∧ (family.baseBottom 1 + verticalMargin + height - (family.baseTop 1 - verticalMargin) : Int) = extentY ∧ (familyDual.baseBottom 1 + verticalMargin + heightDual - (familyDual.baseTop 1 - verticalMargin) : Int) = extentY := by
-- proof
  apply StatMech.FK.PeriodicPlanar.exists_pairedMixedGridDimensions E Edual family familyDual horizontalMargin verticalMargin minimumX minimumY

/--
[exists_pairedMixedBoundaryScores](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldDualBoundaryBands.lean)
-/
@[path]
private lemma exists_pairedMixedBoundaryScores_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {muDual : Measure (ConfigSpace (Sym2 W))}
  [IsProbabilityMeasure muDual]
  {S : Finset V}
  {Sdual : Finset W}
  {p pDual : Real}
  {family : E.NormalBoundaryBandFamily mu S p}
  {familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual}
  {verticalRequirement horizontalRequirement : Nat → Nat}
  {schedule : PairedAlignedMarginSchedule E Edual family familyDual verticalRequirement horizontalRequirement}
  {k : Nat}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (hTIDual : Pdual.IsTranslationInvariant muDual) :
-- imply
  Nonempty (PairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.exists_pairedMixedBoundaryScores E Edual mu muDual hTI hTIDual family familyDual schedule k

/--
[exists_pairedCofinalNormalBoundaryBandFamilies_bounded](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldDualBoundaryBands.lean)
-/
@[path]
private lemma exists_pairedCofinalNormalBoundaryBandFamilies_bounded_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {muDual : Measure (ConfigSpace (Sym2 W))}
  [IsProbabilityMeasure muDual]
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hFKGDual : IsFKG muDual)
  (hTIDual : Pdual.IsTranslationInvariant muDual)
  (huniqueDual : muDual {eta | Pdual.HasUniqueInfiniteCluster eta} = 1) :
-- imply
  ∃ (p pDual : Nat → Real) (family : ∀ m, E.NormalBoundaryBandFamily mu (P.orbitBox m) (p m)) (familyDual : ∀ m, Edual.NormalBoundaryBandFamily muDual (Pdual.orbitBox m) (pDual m)), Tendsto p atTop (nhds 1) ∧ (∀ m, p m ≤ 1) ∧ Tendsto pDual atTop (nhds 1) ∧ (∀ m, pDual m ≤ 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.exists_pairedCofinalNormalBoundaryBandFamilies_bounded E Edual mu muDual hFKG hTI hunique hFKGDual hTIDual huniqueDual

/--
[exists_pairedCofinalMatchedCommonSquareNormalBoundaryBandData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldDualBoundaryBands.lean)
-/
@[path]
private lemma exists_pairedCofinalMatchedCommonSquareNormalBoundaryBandData_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {muDual : Measure (ConfigSpace (Sym2 W))}
  [IsProbabilityMeasure muDual]
  {margin : Nat → Nat}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hFKGDual : IsFKG muDual)
  (hTIDual : Pdual.IsTranslationInvariant muDual)
  (huniqueDual : muDual {eta | Pdual.HasUniqueInfiniteCluster eta} = 1) :
-- imply
  ∃ (p pDual : Nat → Real) (family : ∀ m, E.NormalBoundaryBandFamily mu (P.orbitBox m) (p m)) (familyDual : ∀ m, Edual.NormalBoundaryBandFamily muDual (Pdual.orbitBox m) (pDual m)) (M : Nat → Nat), (∀ m, Nonempty (E.CommonSquareNormalBoundaryBandData mu (P.orbitBox m) (margin m) (M m) (p m))) ∧ (∀ m, Nonempty (Edual.CommonSquareNormalBoundaryBandData muDual (Pdual.orbitBox m) (margin m) (M m) (pDual m))) ∧ Tendsto p atTop (nhds 1) ∧ (∀ m, p m ≤ 1) ∧ Tendsto pDual atTop (nhds 1) ∧ (∀ m, pDual m ≤ 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.exists_pairedCofinalMatchedCommonSquareNormalBoundaryBandData E Edual mu muDual hFKG hTI hunique hFKGDual hTIDual huniqueDual margin

/--
[exists_pairedUniformConnectorRadii_with_commonHalfWidthData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldDualBoundaryBands.lean)
-/
@[path]
private lemma exists_pairedUniformConnectorRadii_with_commonHalfWidthData_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {muDual : Measure (ConfigSpace (Sym2 W))}
  [IsProbabilityMeasure muDual]
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hFKGDual : IsFKG muDual)
  (hTIDual : Pdual.IsTranslationInvariant muDual)
  (huniqueDual : muDual {eta | Pdual.HasUniqueInfiniteCluster eta} = 1) :
-- imply
  ∃ (radius radiusDual : Nat → Nat), E.UniformConnectorCrossingRadius mu radius ∧ Edual.UniformConnectorCrossingRadius muDual radiusDual ∧ ∃ (primal : E.ConnectorReadyCommonSquareData mu radius) (dual : Edual.ConnectorReadyCommonSquareData muDual radiusDual), primal.M = dual.M := by
-- proof
  apply StatMech.FK.PeriodicPlanar.exists_pairedUniformConnectorRadii_with_commonHalfWidthData E Edual mu muDual hFKG hTI hunique hFKGDual hTIDual huniqueDual

/--
[PeriodicPlanarDualPair.exists_canonicalMatchedBoundaryBands_of_common](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldDualBoundaryBands.lean)
-/
@[path]
private lemma exists_canonicalMatchedBoundaryBands_of_common_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {p q : Real}
  {margin : Nat → Nat}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hcommon : let mu : Measure (ConfigSpace (Sym2 V)) := P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) mu D.commonUniqueInfiniteClusterEvent = 1) :
-- imply
  let mu : Measure (ConfigSpace (Sym2 V)) := P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) let muDual : Measure (ConfigSpace (Sym2 W)) := D.dualMeasure mu ∃ (score scoreDual : Nat → Real) (family : ∀ m, D.primalEmbedding.NormalBoundaryBandFamily mu (P.orbitBox m) (score m)) (familyDual : ∀ m, D.dualEmbedding.NormalBoundaryBandFamily muDual (Pdual.orbitBox m) (scoreDual m)) (M : Nat → Nat), (∀ m, Nonempty (D.primalEmbedding.CommonSquareNormalBoundaryBandData mu (P.orbitBox m) (margin m) (M m) (score m))) ∧ (∀ m, Nonempty (D.dualEmbedding.CommonSquareNormalBoundaryBandData muDual (Pdual.orbitBox m) (margin m) (M m) (scoreDual m))) ∧ Tendsto score atTop (nhds 1) ∧ (∀ m, score m ≤ 1) ∧ Tendsto scoreDual atTop (nhds 1) ∧ (∀ m, scoreDual m ≤ 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.exists_canonicalMatchedBoundaryBands_of_common D hp hp1 hq hcommon margin

/--
[PeriodicPlanarDualPair.exists_canonicalConnectorReadyData_of_common](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldDualBoundaryBands.lean)
-/
@[path]
private lemma exists_canonicalConnectorReadyData_of_common_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hcommon : let mu : Measure (ConfigSpace (Sym2 V)) := P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) mu D.commonUniqueInfiniteClusterEvent = 1) :
-- imply
  let mu : Measure (ConfigSpace (Sym2 V)) := P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) let muDual : Measure (ConfigSpace (Sym2 W)) := D.dualMeasure mu ∃ (radius radiusDual : Nat → Nat), D.primalEmbedding.UniformConnectorCrossingRadius mu radius ∧ D.dualEmbedding.UniformConnectorCrossingRadius muDual radiusDual ∧ ∃ (primal : D.primalEmbedding.ConnectorReadyCommonSquareData mu radius) (dual : D.dualEmbedding.ConnectorReadyCommonSquareData muDual radiusDual), primal.M = dual.M := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.exists_canonicalConnectorReadyData_of_common D hp hp1 hq hcommon


-- created on 2026-10-23
