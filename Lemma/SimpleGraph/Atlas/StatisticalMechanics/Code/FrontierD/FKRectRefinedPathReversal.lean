import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectRefinedPathReversal
open StatMech StatMech.FrontierD


/--
[fkRectIntegralSquareDartEnd_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedPathReversal.lean)
-/
@[path]
private lemma fkRectIntegralSquareDartEnd_reverse_eq
  {d : FKRectIntegralSquareDart} :
-- imply
  fkRectIntegralSquareDartEnd (fkRectIntegralSquareDartReverse d) = d.1 := by
-- proof
  apply StatMech.FrontierD.fkRectIntegralSquareDartEnd_reverse d

/--
[FKRectIntegralSquareDartPath.reverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedPathReversal.lean)
-/
@[path]
private lemma reverse_eq
  {p q : Int × Int}
  {l : List FKRectIntegralSquareDart}
-- given
  (h : FKRectIntegralSquareDartPath p q l) :
-- imply
  FKRectIntegralSquareDartPath q p (fkRectIntegralSquareDartListReverse l) := by
-- proof
  apply StatMech.FrontierD.FKRectIntegralSquareDartPath.reverse h

/--
[fkRectIntegralSquareDartReverse_translate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedPathReversal.lean)
-/
@[path]
private lemma fkRectIntegralSquareDartReverse_translate_eq
  {t : Int × Int}
  {d : FKRectIntegralSquareDart} :
-- imply
  fkRectIntegralSquareDartReverse (fkRectIntegralSquareDartTranslate t d) = fkRectIntegralSquareDartTranslate t (fkRectIntegralSquareDartReverse d) := by
-- proof
  apply StatMech.FrontierD.fkRectIntegralSquareDartReverse_translate t d

/--
[fkRectIntegralSquareDartListReverse_translate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedPathReversal.lean)
-/
@[path]
private lemma fkRectIntegralSquareDartListReverse_translate_eq
  {t : Int × Int}
  {l : List FKRectIntegralSquareDart} :
-- imply
  fkRectIntegralSquareDartListReverse (l.map (fkRectIntegralSquareDartTranslate t)) = (fkRectIntegralSquareDartListReverse l).map (fkRectIntegralSquareDartTranslate t) := by
-- proof
  apply StatMech.FrontierD.fkRectIntegralSquareDartListReverse_translate t l

/--
[fkRectIntegralSquareDartMod_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedPathReversal.lean)
-/
@[path]
private lemma fkRectIntegralSquareDartMod_reverse_eq
  {L : Nat}
  {d : FKRectIntegralSquareDart} :
-- imply
  fkRectIntegralSquareDartMod L (fkRectIntegralSquareDartReverse d) = ons_dartRev L (fkRectIntegralSquareDartMod L d) := by
-- proof
  apply StatMech.FrontierD.fkRectIntegralSquareDartMod_reverse L d

/--
[fkRectRefinedRawInteraction_reverse_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedPathReversal.lean)
-/
@[path]
private lemma fkRectRefinedRawInteraction_reverse_right_eq
  {L : Nat}
  [Fact (8 < L)]
  {a b : List (ons_Dart L)} :
-- imply
  fkRectRefinedRawInteraction a (b.reverse.map (ons_dartRev L)) = -fkRectRefinedRawInteraction a b := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedRawInteraction_reverse_right a b

/--
[fkRectRefinedRawInteraction_integralReverse_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedPathReversal.lean)
-/
@[path]
private lemma fkRectRefinedRawInteraction_integralReverse_right_eq
  {L : Nat}
  [Fact (8 < L)]
  {a : List (ons_Dart L)}
  {b : List FKRectIntegralSquareDart} :
-- imply
  fkRectRefinedRawInteraction a ((fkRectIntegralSquareDartListReverse b).map (fkRectIntegralSquareDartMod L)) = -fkRectRefinedRawInteraction a (b.map (fkRectIntegralSquareDartMod L)) := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedRawInteraction_integralReverse_right a b

/--
[fkRectRefinedRawInteraction_translated_boundary_openEdgeReverse_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedPathReversal.lean)
-/
@[path]
private lemma fkRectRefinedRawInteraction_translated_boundary_openEdgeReverse_eq_zero_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
  {d : FKMedialDart R.medialTorus}
  {n : Nat}
  {a b u : Int × Int}
-- given
  (heF : e ∈ F)
  (hrelative : (a.1 - b.1, a.2 - b.2) = (4 * (fkRectSquareDeckTranslation R u).1, 4 * (fkRectSquareDeckTranslation R u).2)) :
-- imply
  let pairing := fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F) let c := fkRectRefinedBoundaryCanonicalCenter R d let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R) fkRectRefinedRawInteraction (((fkRectRefinedBoundaryDarts pairing d c n).map (fkRectIntegralSquareDartTranslate a)).map (fkRectIntegralSquareDartMod L)) (((fkRectIntegralSquareDartListReverse (fkRectRefinedPrimalEdgeDarts R e)).map (fkRectIntegralSquareDartTranslate b)).map (fkRectIntegralSquareDartMod L)) = 0 := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedRawInteraction_translated_boundary_openEdgeReverse_eq_zero R F e heF d n a b u hrelative

/--
[fkRectRefinedRawInteraction_repeated_boundary_openEdgeReverse_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedPathReversal.lean)
-/
@[path]
private lemma fkRectRefinedRawInteraction_repeated_boundary_openEdgeReverse_eq_zero_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
  {d : FKMedialDart R.medialTorus}
  {n : Nat}
  {w z : Int × Int}
-- given
  (heF : e ∈ F) :
-- imply
  let pairing := fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F) let c := fkRectRefinedBoundaryCanonicalCenter R d let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R) let U : Int × Int := (4 * (fkRectSquareDeckTranslation R w).1, 4 * (fkRectSquareDeckTranslation R w).2) let V : Int × Int := (4 * (fkRectSquareDeckTranslation R z).1, 4 * (fkRectSquareDeckTranslation R z).2) fkRectRefinedRawInteraction ((fkRectRepeatTranslatedDartPath (fkRectRefinedBoundaryDarts pairing d c n) U L).map (fkRectIntegralSquareDartMod L)) ((fkRectRepeatTranslatedDartPath (fkRectIntegralSquareDartListReverse (fkRectRefinedPrimalEdgeDarts R e)) V L).map (fkRectIntegralSquareDartMod L)) = 0 := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedRawInteraction_repeated_boundary_openEdgeReverse_eq_zero R F e heF d n w z


-- created on 2026-10-23
