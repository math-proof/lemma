import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryPotentialContradiction
open StatMech StatMech.FrontierD


/--
[fkRectRepeatDartList_balanced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryPotentialContradiction.lean)
-/
@[path]
private lemma fkRectRepeatDartList_balanced_eq
  {L : Nat}
  [Fact (8 < L)]
  {n : Nat}
  {l : List (StatMech.Onsager.ons_Dart L)}
-- given
  (hl : DartListBalanced l) :
-- imply
  DartListBalanced (fkRectRepeatDartList n l) := by
-- proof
  apply StatMech.FrontierD.fkRectRepeatDartList_balanced n l hl

/--
[fkRectRepeatDartList_map_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryPotentialContradiction.lean)
-/
@[path]
private lemma fkRectRepeatDartList_map_sum_eq
  {n : Nat}
  {l : List alpha}
  {f : alpha → Int} :
-- imply
  ((fkRectRepeatDartList n l).map f).sum = (n : Int) * (l.map f).sum := by
-- proof
  apply StatMech.FrontierD.fkRectRepeatDartList_map_sum n l f

/--
[fkRectRefinedRawInteraction_repeatDartList_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryPotentialContradiction.lean)
-/
@[path]
private lemma fkRectRefinedRawInteraction_repeatDartList_left_eq
  {L : Nat}
  [Fact (8 < L)]
  {n : Nat}
  {a b : List (StatMech.Onsager.ons_Dart L)} :
-- imply
  fkRectRefinedRawInteraction (fkRectRepeatDartList n a) b = (n : Int) * fkRectRefinedRawInteraction a b := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedRawInteraction_repeatDartList_left n a b

/--
[int_natAbs_cross_mul_eq_of_mul_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryPotentialContradiction.lean)
-/
@[path]
private lemma int_natAbs_cross_mul_eq_of_mul_pos_eq
  {a b : Int}
-- given
  (h : 0 < a * b) :
-- imply
  (b.natAbs : Int) * a = (a.natAbs : Int) * b := by
-- proof
  apply StatMech.FrontierD.int_natAbs_cross_mul_eq_of_mul_pos a b h

/--
[fkRectCanonicalRefinedBoundaryOrbitCoverDarts_xWrap_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryPotentialContradiction.lean)
-/
@[path]
private lemma fkRectCanonicalRefinedBoundaryOrbitCoverDarts_xWrap_eq_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialDart R.medialTorus} :
-- imply
  ((fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega d).map StatMech.Onsager.ons_xWrapSign).sum = 4 * (fkRectSquareDeckTranslation R (fkRectWalkWinding R (fkRectMedialBoundaryPrimalOrbitWalk R omega d))).1 := by
-- proof
  apply StatMech.FrontierD.fkRectCanonicalRefinedBoundaryOrbitCoverDarts_xWrap_eq R omega d

/--
[fkRectCanonicalRefinedBoundaryOrbitCoverDarts_yWrap_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryPotentialContradiction.lean)
-/
@[path]
private lemma fkRectCanonicalRefinedBoundaryOrbitCoverDarts_yWrap_eq_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialDart R.medialTorus} :
-- imply
  ((fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega d).map StatMech.Onsager.ons_yWrapSign).sum = 4 * (fkRectSquareDeckTranslation R (fkRectWalkWinding R (fkRectMedialBoundaryPrimalOrbitWalk R omega d))).2 := by
-- proof
  apply StatMech.FrontierD.fkRectCanonicalRefinedBoundaryOrbitCoverDarts_yWrap_eq R omega d

/--
[fkRectBalancedCarriers_localPotential_contradiction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryPotentialContradiction.lean)
-/
@[path]
private lemma fkRectBalancedCarriers_localPotential_contradiction_eq
  {L : Nat}
  [Fact (8 < L)]
  {A B : List (StatMech.Onsager.ons_Dart L)}
  {p q : Int × Int}
  {l m : List FKRectIntegralSquareDart}
-- given
  (hAbal : DartListBalanced A)
  (hBbal : DartListBalanced B)
  (hl : FKRectIntegralSquareDartPath p q l)
  (hm : FKRectIntegralSquareDartPath p q m)
  (hx : (A.map StatMech.Onsager.ons_xWrapSign).sum = (B.map StatMech.Onsager.ons_xWrapSign).sum)
  (hy : (A.map StatMech.Onsager.ons_yWrapSign).sum = (B.map StatMech.Onsager.ons_yWrapSign).sum)
  (hAopen : fkRectRefinedRawInteraction A (l.map (fkRectIntegralSquareDartMod L)) = 0)
  (hBopen : fkRectRefinedRawInteraction B (l.map (fkRectIntegralSquareDartMod L)) = 0)
  (hAlocal : fkRectRefinedRawInteraction A (m.map (fkRectIntegralSquareDartMod L)) ≠ 0)
  (hBlocal : fkRectRefinedRawInteraction B (m.map (fkRectIntegralSquareDartMod L)) = 0) :
-- imply
  False := by
-- proof
  apply StatMech.FrontierD.fkRectBalancedCarriers_localPotential_contradiction A B hAbal hBbal hl hm hx hy hAopen hBopen hAlocal hBlocal

/--
[fkRectBalancedCarriers_equalFlux_signed_contradiction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryPotentialContradiction.lean)
-/
@[path]
private lemma fkRectBalancedCarriers_equalFlux_signed_contradiction_eq
  {L : Nat}
  [Fact (8 < L)]
  {A B : List (StatMech.Onsager.ons_Dart L)}
  {p q : Int × Int}
  {l m : List FKRectIntegralSquareDart}
-- given
  (hAbal : DartListBalanced A)
  (hBbal : DartListBalanced B)
  (hl : FKRectIntegralSquareDartPath p q l)
  (hm : FKRectIntegralSquareDartPath p q m)
  (hx : (A.map StatMech.Onsager.ons_xWrapSign).sum = (B.map StatMech.Onsager.ons_xWrapSign).sum)
  (hy : (A.map StatMech.Onsager.ons_yWrapSign).sum = (B.map StatMech.Onsager.ons_yWrapSign).sum)
  (hAopen : fkRectRefinedRawInteraction A (l.map (fkRectIntegralSquareDartMod L)) = 0)
  (hBopen : fkRectRefinedRawInteraction B (l.map (fkRectIntegralSquareDartMod L)) = 0)
  (hAlocal : 0 < fkRectRefinedRawInteraction A (m.map (fkRectIntegralSquareDartMod L)))
  (hBlocal : fkRectRefinedRawInteraction B (m.map (fkRectIntegralSquareDartMod L)) ≤ 0) :
-- imply
  False := by
-- proof
  apply StatMech.FrontierD.fkRectBalancedCarriers_equalFlux_signed_contradiction A B hAbal hBbal hl hm hx hy hAopen hBopen hAlocal hBlocal

/--
[fkRectBalancedCarriers_sameSignHorizontal_signed_contradiction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryPotentialContradiction.lean)
-/
@[path]
private lemma fkRectBalancedCarriers_sameSignHorizontal_signed_contradiction_eq
  {L : Nat}
  [Fact (8 < L)]
  {A B : List (StatMech.Onsager.ons_Dart L)}
  {p q : Int × Int}
  {l m : List FKRectIntegralSquareDart}
-- given
  (hAbal : DartListBalanced A)
  (hBbal : DartListBalanced B)
  (hl : FKRectIntegralSquareDartPath p q l)
  (hm : FKRectIntegralSquareDartPath p q m)
  (hxsign : 0 < (A.map StatMech.Onsager.ons_xWrapSign).sum * (B.map StatMech.Onsager.ons_xWrapSign).sum)
  (hyA : (A.map StatMech.Onsager.ons_yWrapSign).sum = 0)
  (hyB : (B.map StatMech.Onsager.ons_yWrapSign).sum = 0)
  (hAopen : fkRectRefinedRawInteraction A (l.map (fkRectIntegralSquareDartMod L)) = 0)
  (hBopen : fkRectRefinedRawInteraction B (l.map (fkRectIntegralSquareDartMod L)) = 0)
  (hAlocal : 0 < fkRectRefinedRawInteraction A (m.map (fkRectIntegralSquareDartMod L)))
  (hBlocal : fkRectRefinedRawInteraction B (m.map (fkRectIntegralSquareDartMod L)) ≤ 0) :
-- imply
  False := by
-- proof
  apply StatMech.FrontierD.fkRectBalancedCarriers_sameSignHorizontal_signed_contradiction A B hAbal hBbal hl hm hxsign hyA hyB hAopen hBopen hAlocal hBlocal

/--
[fkRectBalancedCarriers_sameSignDiagonal_signed_contradiction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryPotentialContradiction.lean)
-/
@[path]
private lemma fkRectBalancedCarriers_sameSignDiagonal_signed_contradiction_eq
  {L : Nat}
  [Fact (8 < L)]
  {A B : List (StatMech.Onsager.ons_Dart L)}
  {p q : Int × Int}
  {l m : List FKRectIntegralSquareDart}
-- given
  (hAbal : DartListBalanced A)
  (hBbal : DartListBalanced B)
  (hl : FKRectIntegralSquareDartPath p q l)
  (hm : FKRectIntegralSquareDartPath p q m)
  (hxsign : 0 < (A.map StatMech.Onsager.ons_xWrapSign).sum * (B.map StatMech.Onsager.ons_xWrapSign).sum)
  (hdiagA : (A.map StatMech.Onsager.ons_yWrapSign).sum = (A.map StatMech.Onsager.ons_xWrapSign).sum)
  (hdiagB : (B.map StatMech.Onsager.ons_yWrapSign).sum = (B.map StatMech.Onsager.ons_xWrapSign).sum)
  (hAopen : fkRectRefinedRawInteraction A (l.map (fkRectIntegralSquareDartMod L)) = 0)
  (hBopen : fkRectRefinedRawInteraction B (l.map (fkRectIntegralSquareDartMod L)) = 0)
  (hAlocal : 0 < fkRectRefinedRawInteraction A (m.map (fkRectIntegralSquareDartMod L)))
  (hBlocal : fkRectRefinedRawInteraction B (m.map (fkRectIntegralSquareDartMod L)) ≤ 0) :
-- imply
  False := by
-- proof
  apply StatMech.FrontierD.fkRectBalancedCarriers_sameSignDiagonal_signed_contradiction A B hAbal hBbal hl hm hxsign hdiagA hdiagB hAopen hBopen hAlocal hBlocal

/--
[fkRectBalancedCarriers_sameSignHorizontal_target_contradiction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryPotentialContradiction.lean)
-/
@[path]
private lemma fkRectBalancedCarriers_sameSignHorizontal_target_contradiction_eq
  {L : Nat}
  [Fact (8 < L)]
  {A B C : List (StatMech.Onsager.ons_Dart L)}
-- given
  (hAbal : DartListBalanced A)
  (hBbal : DartListBalanced B)
  (hCbal : DartListBalanced C)
  (hxsign : 0 < (A.map StatMech.Onsager.ons_xWrapSign).sum * (B.map StatMech.Onsager.ons_xWrapSign).sum)
  (hyA : (A.map StatMech.Onsager.ons_yWrapSign).sum = 0)
  (hyB : (B.map StatMech.Onsager.ons_yWrapSign).sum = 0)
  (hAC : 0 < fkRectRefinedRawInteraction A C)
  (hBC : fkRectRefinedRawInteraction B C ≤ 0) :
-- imply
  False := by
-- proof
  apply StatMech.FrontierD.fkRectBalancedCarriers_sameSignHorizontal_target_contradiction A B C hAbal hBbal hCbal hxsign hyA hyB hAC hBC

/--
[fkRectBalancedCarriers_sameSignDiagonal_target_contradiction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryPotentialContradiction.lean)
-/
@[path]
private lemma fkRectBalancedCarriers_sameSignDiagonal_target_contradiction_eq
  {L : Nat}
  [Fact (8 < L)]
  {A B C : List (StatMech.Onsager.ons_Dart L)}
-- given
  (hAbal : DartListBalanced A)
  (hBbal : DartListBalanced B)
  (hCbal : DartListBalanced C)
  (hxsign : 0 < (A.map StatMech.Onsager.ons_xWrapSign).sum * (B.map StatMech.Onsager.ons_xWrapSign).sum)
  (hdiagA : (A.map StatMech.Onsager.ons_yWrapSign).sum = (A.map StatMech.Onsager.ons_xWrapSign).sum)
  (hdiagB : (B.map StatMech.Onsager.ons_yWrapSign).sum = (B.map StatMech.Onsager.ons_xWrapSign).sum)
  (hAC : 0 < fkRectRefinedRawInteraction A C)
  (hBC : fkRectRefinedRawInteraction B C ≤ 0) :
-- imply
  False := by
-- proof
  apply StatMech.FrontierD.fkRectBalancedCarriers_sameSignDiagonal_target_contradiction A B C hAbal hBbal hCbal hxsign hdiagA hdiagB hAC hBC

/--
[fkRectBalancedCarriers_sameSignDiagonal_target_contradiction_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryPotentialContradiction.lean)
-/
@[path]
private lemma fkRectBalancedCarriers_sameSignDiagonal_target_contradiction_neg_eq
  {L : Nat}
  [Fact (8 < L)]
  {A B C : List (StatMech.Onsager.ons_Dart L)}
-- given
  (hAbal : DartListBalanced A)
  (hBbal : DartListBalanced B)
  (hCbal : DartListBalanced C)
  (hxsign : 0 < (A.map StatMech.Onsager.ons_xWrapSign).sum * (B.map StatMech.Onsager.ons_xWrapSign).sum)
  (hdiagA : (A.map StatMech.Onsager.ons_yWrapSign).sum = (A.map StatMech.Onsager.ons_xWrapSign).sum)
  (hdiagB : (B.map StatMech.Onsager.ons_yWrapSign).sum = (B.map StatMech.Onsager.ons_xWrapSign).sum)
  (hAC : fkRectRefinedRawInteraction A C < 0)
  (hBC : 0 ≤ fkRectRefinedRawInteraction B C) :
-- imply
  False := by
-- proof
  apply StatMech.FrontierD.fkRectBalancedCarriers_sameSignDiagonal_target_contradiction_neg A B C hAbal hBbal hCbal hxsign hdiagA hdiagB hAC hBC

/--
[fkRectCanonicalBoundaryCarriers_repeatedInsertionTarget_contradiction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryPotentialContradiction.lean)
-/
@[path]
private lemma fkRectCanonicalBoundaryCarriers_repeatedInsertionTarget_contradiction_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
  {dB : FKMedialDart R.medialTorus}
  {l : List FKRectIntegralSquareDart}
  {z : Int × Int}
-- given
  (heF : e ∉ F)
  (hsep : ¬ (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F))).Reachable (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) (fkMedialEastDart (fkRectMedialVertexOfEdge R e)))
  (hcolor : fkMedialCheckerColor dB = fkMedialCheckerColor (fkMedialWestDart (fkRectMedialVertexOfEdge R e)))
  (hBsep : ¬ (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F))).Reachable (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) dB)
  (hblocks : FKRectRefinedOpenEdgeBlocks R F l)
  (hTbal : let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R) let V : Int × Int := (4 * (fkRectSquareDeckTranslation R z).1, 4 * (fkRectSquareDeckTranslation R z).2) DartListBalanced ((fkRectRepeatTranslatedDartPath (fkRectRefinedPrimalEdgeDarts R e ++ l) V L).map (fkRectIntegralSquareDartMod L)))
  (hxsign : let omega := fkRectConfigurationOfEdges R F let dA := fkMedialWestDart (fkRectMedialVertexOfEdge R e) let A := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dA let B := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dB 0 < (A.map StatMech.Onsager.ons_xWrapSign).sum * (B.map StatMech.Onsager.ons_xWrapSign).sum)
  (hyA : let omega := fkRectConfigurationOfEdges R F let dA := fkMedialWestDart (fkRectMedialVertexOfEdge R e) let A := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dA (A.map StatMech.Onsager.ons_yWrapSign).sum = 0)
  (hyB : let omega := fkRectConfigurationOfEdges R F let B := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dB (B.map StatMech.Onsager.ons_yWrapSign).sum = 0) :
-- imply
  False := by
-- proof
  apply StatMech.FrontierD.fkRectCanonicalBoundaryCarriers_repeatedInsertionTarget_contradiction R F e heF hsep dB hcolor hBsep hblocks z hTbal hxsign hyA hyB

/--
[fkRectCanonicalBoundaryCarriers_repeatedInsertionTarget_diagonal_contradiction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryPotentialContradiction.lean)
-/
@[path]
private lemma fkRectCanonicalBoundaryCarriers_repeatedInsertionTarget_diagonal_contradiction_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
  {dB : FKMedialDart R.medialTorus}
  {l : List FKRectIntegralSquareDart}
  {z : Int × Int}
-- given
  (heF : e ∉ F)
  (hsep : ¬ (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F))).Reachable (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) (fkMedialEastDart (fkRectMedialVertexOfEdge R e)))
  (hcolor : fkMedialCheckerColor dB = fkMedialCheckerColor (fkMedialWestDart (fkRectMedialVertexOfEdge R e)))
  (hBsep : ¬ (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F))).Reachable (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) dB)
  (hblocks : FKRectRefinedOpenEdgeBlocks R F l)
  (hTbal : let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R) let V : Int × Int := (4 * (fkRectSquareDeckTranslation R z).1, 4 * (fkRectSquareDeckTranslation R z).2) DartListBalanced ((fkRectRepeatTranslatedDartPath (fkRectRefinedPrimalEdgeDarts R e ++ l) V L).map (fkRectIntegralSquareDartMod L)))
  (hxsign : let omega := fkRectConfigurationOfEdges R F let dA := fkMedialWestDart (fkRectMedialVertexOfEdge R e) let A := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dA let B := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dB 0 < (A.map StatMech.Onsager.ons_xWrapSign).sum * (B.map StatMech.Onsager.ons_xWrapSign).sum)
  (hdiagA : let omega := fkRectConfigurationOfEdges R F let dA := fkMedialWestDart (fkRectMedialVertexOfEdge R e) let A := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dA (A.map StatMech.Onsager.ons_yWrapSign).sum = (A.map StatMech.Onsager.ons_xWrapSign).sum)
  (hdiagB : let omega := fkRectConfigurationOfEdges R F let B := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dB (B.map StatMech.Onsager.ons_yWrapSign).sum = (B.map StatMech.Onsager.ons_xWrapSign).sum) :
-- imply
  False := by
-- proof
  apply StatMech.FrontierD.fkRectCanonicalBoundaryCarriers_repeatedInsertionTarget_diagonal_contradiction R F e heF hsep dB hcolor hBsep hblocks z hTbal hxsign hdiagA hdiagB

/--
[fkRectCanonicalBoundaryCarriers_repeatedInsertionTarget_diagonal_contradiction_east](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryPotentialContradiction.lean)
-/
@[path]
private lemma fkRectCanonicalBoundaryCarriers_repeatedInsertionTarget_diagonal_contradiction_east_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
  {dB : FKMedialDart R.medialTorus}
  {l : List FKRectIntegralSquareDart}
  {z : Int × Int}
-- given
  (heF : e ∉ F)
  (hsep : ¬ (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F))).Reachable (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) (fkMedialEastDart (fkRectMedialVertexOfEdge R e)))
  (hcolor : fkMedialCheckerColor dB = fkMedialCheckerColor (fkMedialEastDart (fkRectMedialVertexOfEdge R e)))
  (hBsep : ¬ (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F))).Reachable (fkMedialEastDart (fkRectMedialVertexOfEdge R e)) dB)
  (hblocks : FKRectRefinedOpenEdgeBlocks R F l)
  (hTbal : let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R) let V : Int × Int := (4 * (fkRectSquareDeckTranslation R z).1, 4 * (fkRectSquareDeckTranslation R z).2) DartListBalanced ((fkRectRepeatTranslatedDartPath (fkRectRefinedPrimalEdgeDarts R e ++ l) V L).map (fkRectIntegralSquareDartMod L)))
  (hxsign : let omega := fkRectConfigurationOfEdges R F let dA := fkMedialEastDart (fkRectMedialVertexOfEdge R e) let A := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dA let B := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dB 0 < (A.map StatMech.Onsager.ons_xWrapSign).sum * (B.map StatMech.Onsager.ons_xWrapSign).sum)
  (hdiagA : let omega := fkRectConfigurationOfEdges R F let dA := fkMedialEastDart (fkRectMedialVertexOfEdge R e) let A := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dA (A.map StatMech.Onsager.ons_yWrapSign).sum = (A.map StatMech.Onsager.ons_xWrapSign).sum)
  (hdiagB : let omega := fkRectConfigurationOfEdges R F let B := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dB (B.map StatMech.Onsager.ons_yWrapSign).sum = (B.map StatMech.Onsager.ons_xWrapSign).sum) :
-- imply
  False := by
-- proof
  apply StatMech.FrontierD.fkRectCanonicalBoundaryCarriers_repeatedInsertionTarget_diagonal_contradiction_east R F e heF hsep dB hcolor hBsep hblocks z hTbal hxsign hdiagA hdiagB

/--
[fkRectConnectedInsertion_distinct_sameSignHorizontal_contradiction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryPotentialContradiction.lean)
-/
@[path]
private lemma fkRectConnectedInsertion_distinct_sameSignHorizontal_contradiction_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
  {r : (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Walk (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e)}
  {dB : FKMedialDart R.medialTorus}
-- given
  (heF : e ∉ F)
  (hsep : ¬ (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F))).Reachable (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) (fkMedialEastDart (fkRectMedialVertexOfEdge R e)))
  (hcolor : fkMedialCheckerColor dB = fkMedialCheckerColor (fkMedialWestDart (fkRectMedialVertexOfEdge R e)))
  (hBsep : ¬ (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F))).Reachable (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) dB)
  (hxsign : let omega := fkRectConfigurationOfEdges R F let dA := fkMedialWestDart (fkRectMedialVertexOfEdge R e) let A := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dA let B := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dB 0 < (A.map StatMech.Onsager.ons_xWrapSign).sum * (B.map StatMech.Onsager.ons_xWrapSign).sum)
  (hyA : let omega := fkRectConfigurationOfEdges R F let dA := fkMedialWestDart (fkRectMedialVertexOfEdge R e) let A := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dA (A.map StatMech.Onsager.ons_yWrapSign).sum = 0)
  (hyB : let omega := fkRectConfigurationOfEdges R F let B := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dB (B.map StatMech.Onsager.ons_yWrapSign).sum = 0) :
-- imply
  False := by
-- proof
  apply StatMech.FrontierD.fkRectConnectedInsertion_distinct_sameSignHorizontal_contradiction R F e r heF hsep dB hcolor hBsep hxsign hyA hyB

/--
[fkRectConnectedInsertion_distinct_sameSignDiagonal_contradiction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryPotentialContradiction.lean)
-/
@[path]
private lemma fkRectConnectedInsertion_distinct_sameSignDiagonal_contradiction_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
  {r : (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Walk (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e)}
  {dB : FKMedialDart R.medialTorus}
-- given
  (heF : e ∉ F)
  (hsep : ¬ (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F))).Reachable (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) (fkMedialEastDart (fkRectMedialVertexOfEdge R e)))
  (hcolor : fkMedialCheckerColor dB = fkMedialCheckerColor (fkMedialWestDart (fkRectMedialVertexOfEdge R e)))
  (hBsep : ¬ (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F))).Reachable (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) dB)
  (hxsign : let omega := fkRectConfigurationOfEdges R F let dA := fkMedialWestDart (fkRectMedialVertexOfEdge R e) let A := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dA let B := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dB 0 < (A.map StatMech.Onsager.ons_xWrapSign).sum * (B.map StatMech.Onsager.ons_xWrapSign).sum)
  (hdiagA : let omega := fkRectConfigurationOfEdges R F let dA := fkMedialWestDart (fkRectMedialVertexOfEdge R e) let A := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dA (A.map StatMech.Onsager.ons_yWrapSign).sum = (A.map StatMech.Onsager.ons_xWrapSign).sum)
  (hdiagB : let omega := fkRectConfigurationOfEdges R F let B := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dB (B.map StatMech.Onsager.ons_yWrapSign).sum = (B.map StatMech.Onsager.ons_xWrapSign).sum) :
-- imply
  False := by
-- proof
  apply StatMech.FrontierD.fkRectConnectedInsertion_distinct_sameSignDiagonal_contradiction R F e r heF hsep dB hcolor hBsep hxsign hdiagA hdiagB

/--
[fkRectConnectedInsertion_distinct_sameSignDiagonal_contradiction_east](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryPotentialContradiction.lean)
-/
@[path]
private lemma fkRectConnectedInsertion_distinct_sameSignDiagonal_contradiction_east_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
  {r : (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Walk (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e)}
  {dB : FKMedialDart R.medialTorus}
-- given
  (heF : e ∉ F)
  (hsep : ¬ (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F))).Reachable (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) (fkMedialEastDart (fkRectMedialVertexOfEdge R e)))
  (hcolor : fkMedialCheckerColor dB = fkMedialCheckerColor (fkMedialEastDart (fkRectMedialVertexOfEdge R e)))
  (hBsep : ¬ (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F))).Reachable (fkMedialEastDart (fkRectMedialVertexOfEdge R e)) dB)
  (hxsign : let omega := fkRectConfigurationOfEdges R F let dA := fkMedialEastDart (fkRectMedialVertexOfEdge R e) let A := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dA let B := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dB 0 < (A.map StatMech.Onsager.ons_xWrapSign).sum * (B.map StatMech.Onsager.ons_xWrapSign).sum)
  (hdiagA : let omega := fkRectConfigurationOfEdges R F let dA := fkMedialEastDart (fkRectMedialVertexOfEdge R e) let A := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dA (A.map StatMech.Onsager.ons_yWrapSign).sum = (A.map StatMech.Onsager.ons_xWrapSign).sum)
  (hdiagB : let omega := fkRectConfigurationOfEdges R F let B := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dB (B.map StatMech.Onsager.ons_yWrapSign).sum = (B.map StatMech.Onsager.ons_xWrapSign).sum) :
-- imply
  False := by
-- proof
  apply StatMech.FrontierD.fkRectConnectedInsertion_distinct_sameSignDiagonal_contradiction_east R F e r heF hsep dB hcolor hBsep hxsign hdiagA hdiagB

/--
[fkRectConnectedInsertion_distinct_sameSignFKHorizontal_contradiction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryPotentialContradiction.lean)
-/
@[path]
private lemma fkRectConnectedInsertion_distinct_sameSignFKHorizontal_contradiction_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
  {r : (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Walk (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e)}
  {dB : FKMedialDart R.medialTorus}
-- given
  (heF : e ∉ F)
  (hsep : ¬ (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F))).Reachable (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) (fkMedialEastDart (fkRectMedialVertexOfEdge R e)))
  (hcolor : fkMedialCheckerColor dB = fkMedialCheckerColor (fkMedialWestDart (fkRectMedialVertexOfEdge R e)))
  (hBsep : ¬ (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F))).Reachable (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) dB)
  (hxsign : let omega := fkRectConfigurationOfEdges R F let dA := fkMedialWestDart (fkRectMedialVertexOfEdge R e) 0 < (fkRectWalkWinding R (fkRectMedialBoundaryPrimalOrbitWalk R omega dA)).1 * (fkRectWalkWinding R (fkRectMedialBoundaryPrimalOrbitWalk R omega dB)).1)
  (hyA : let omega := fkRectConfigurationOfEdges R F let dA := fkMedialWestDart (fkRectMedialVertexOfEdge R e) (fkRectWalkWinding R (fkRectMedialBoundaryPrimalOrbitWalk R omega dA)).2 = 0)
  (hyB : let omega := fkRectConfigurationOfEdges R F (fkRectWalkWinding R (fkRectMedialBoundaryPrimalOrbitWalk R omega dB)).2 = 0) :
-- imply
  False := by
-- proof
  apply StatMech.FrontierD.fkRectConnectedInsertion_distinct_sameSignFKHorizontal_contradiction R F e r heF hsep dB hcolor hBsep hxsign hyA hyB

/--
[fkRectConnectedInsertion_distinct_sameSignFKHorizontal_contradiction_east](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryPotentialContradiction.lean)
-/
@[path]
private lemma fkRectConnectedInsertion_distinct_sameSignFKHorizontal_contradiction_east_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
  {r : (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Walk (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e)}
  {dB : FKMedialDart R.medialTorus}
-- given
  (heF : e ∉ F)
  (hsep : ¬ (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F))).Reachable (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) (fkMedialEastDart (fkRectMedialVertexOfEdge R e)))
  (hcolor : fkMedialCheckerColor dB = fkMedialCheckerColor (fkMedialEastDart (fkRectMedialVertexOfEdge R e)))
  (hBsep : ¬ (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F))).Reachable (fkMedialEastDart (fkRectMedialVertexOfEdge R e)) dB)
  (hxsign : let omega := fkRectConfigurationOfEdges R F let dA := fkMedialEastDart (fkRectMedialVertexOfEdge R e) 0 < (fkRectWalkWinding R (fkRectMedialBoundaryPrimalOrbitWalk R omega dA)).1 * (fkRectWalkWinding R (fkRectMedialBoundaryPrimalOrbitWalk R omega dB)).1)
  (hyA : let omega := fkRectConfigurationOfEdges R F let dA := fkMedialEastDart (fkRectMedialVertexOfEdge R e) (fkRectWalkWinding R (fkRectMedialBoundaryPrimalOrbitWalk R omega dA)).2 = 0)
  (hyB : let omega := fkRectConfigurationOfEdges R F (fkRectWalkWinding R (fkRectMedialBoundaryPrimalOrbitWalk R omega dB)).2 = 0) :
-- imply
  False := by
-- proof
  apply StatMech.FrontierD.fkRectConnectedInsertion_distinct_sameSignFKHorizontal_contradiction_east R F e r heF hsep dB hcolor hBsep hxsign hyA hyB

/--
[fkRectCanonicalBoundaryCarrier_localPotential_contradiction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryPotentialContradiction.lean)
-/
@[path]
private lemma fkRectCanonicalBoundaryCarrier_localPotential_contradiction_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
  {dB : FKMedialDart R.medialTorus}
  {l : List FKRectIntegralSquareDart}
-- given
  (heF : e ∉ F)
  (hsep : ¬ (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F))).Reachable (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) (fkMedialEastDart (fkRectMedialVertexOfEdge R e)))
  (hl : FKRectIntegralSquareDartPath (fkRectRefinedPrimalEdgeStart R e) (fkRectRefinedPrimalEdgeEnd R e) l)
  (hblocks : FKRectRefinedOpenEdgeBlocks R F l)
  (hx : let omega := fkRectConfigurationOfEdges R F let dA := fkMedialWestDart (fkRectMedialVertexOfEdge R e) let A := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dA let B := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dB (A.map StatMech.Onsager.ons_xWrapSign).sum = (B.map StatMech.Onsager.ons_xWrapSign).sum)
  (hy : let omega := fkRectConfigurationOfEdges R F let dA := fkMedialWestDart (fkRectMedialVertexOfEdge R e) let A := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dA let B := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dB (A.map StatMech.Onsager.ons_yWrapSign).sum = (B.map StatMech.Onsager.ons_yWrapSign).sum)
  (hBedge : let omega := fkRectConfigurationOfEdges R F let B := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dB fkRectRefinedRawInteraction B ((fkRectRefinedPrimalEdgeDarts R e).map (fkRectIntegralSquareDartMod (fkRectSquareCoverSide (fkRectRefinedCoverTorus R)))) = 0) :
-- imply
  False := by
-- proof
  apply StatMech.FrontierD.fkRectCanonicalBoundaryCarrier_localPotential_contradiction R F e heF hsep dB hl hblocks hx hy hBedge

/--
[fkRectCanonicalBoundaryCarrier_sameSignHorizontal_localPotential_contradiction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryPotentialContradiction.lean)
-/
@[path]
private lemma fkRectCanonicalBoundaryCarrier_sameSignHorizontal_localPotential_contradiction_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
  {dB : FKMedialDart R.medialTorus}
  {l : List FKRectIntegralSquareDart}
-- given
  (heF : e ∉ F)
  (hsep : ¬ (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F))).Reachable (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) (fkMedialEastDart (fkRectMedialVertexOfEdge R e)))
  (hl : FKRectIntegralSquareDartPath (fkRectRefinedPrimalEdgeStart R e) (fkRectRefinedPrimalEdgeEnd R e) l)
  (hblocks : FKRectRefinedOpenEdgeBlocks R F l)
  (hxsign : let omega := fkRectConfigurationOfEdges R F let dA := fkMedialWestDart (fkRectMedialVertexOfEdge R e) let A := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dA let B := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dB 0 < (A.map StatMech.Onsager.ons_xWrapSign).sum * (B.map StatMech.Onsager.ons_xWrapSign).sum)
  (hyA : let omega := fkRectConfigurationOfEdges R F let dA := fkMedialWestDart (fkRectMedialVertexOfEdge R e) let A := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dA (A.map StatMech.Onsager.ons_yWrapSign).sum = 0)
  (hyB : let omega := fkRectConfigurationOfEdges R F let B := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dB (B.map StatMech.Onsager.ons_yWrapSign).sum = 0)
  (hBedge : let omega := fkRectConfigurationOfEdges R F let B := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dB fkRectRefinedRawInteraction B ((fkRectRefinedPrimalEdgeDarts R e).map (fkRectIntegralSquareDartMod (fkRectSquareCoverSide (fkRectRefinedCoverTorus R)))) = 0) :
-- imply
  False := by
-- proof
  apply StatMech.FrontierD.fkRectCanonicalBoundaryCarrier_sameSignHorizontal_localPotential_contradiction R F e heF hsep dB hl hblocks hxsign hyA hyB hBedge

/--
[fkRectCanonicalBoundaryCarrier_distinct_sameSignHorizontal_contradiction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryPotentialContradiction.lean)
-/
@[path]
private lemma fkRectCanonicalBoundaryCarrier_distinct_sameSignHorizontal_contradiction_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
  {dB : FKMedialDart R.medialTorus}
  {l : List FKRectIntegralSquareDart}
-- given
  (heF : e ∉ F)
  (hsep : ¬ (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F))).Reachable (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) (fkMedialEastDart (fkRectMedialVertexOfEdge R e)))
  (hcolor : fkMedialCheckerColor dB = fkMedialCheckerColor (fkMedialWestDart (fkRectMedialVertexOfEdge R e)))
  (hBsep : ¬ (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F))).Reachable (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) dB)
  (hl : FKRectIntegralSquareDartPath (fkRectRefinedPrimalEdgeStart R e) (fkRectRefinedPrimalEdgeEnd R e) l)
  (hblocks : FKRectRefinedOpenEdgeBlocks R F l)
  (hxsign : let omega := fkRectConfigurationOfEdges R F let dA := fkMedialWestDart (fkRectMedialVertexOfEdge R e) let A := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dA let B := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dB 0 < (A.map StatMech.Onsager.ons_xWrapSign).sum * (B.map StatMech.Onsager.ons_xWrapSign).sum)
  (hyA : let omega := fkRectConfigurationOfEdges R F let dA := fkMedialWestDart (fkRectMedialVertexOfEdge R e) let A := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dA (A.map StatMech.Onsager.ons_yWrapSign).sum = 0)
  (hyB : let omega := fkRectConfigurationOfEdges R F let B := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dB (B.map StatMech.Onsager.ons_yWrapSign).sum = 0) :
-- imply
  False := by
-- proof
  apply StatMech.FrontierD.fkRectCanonicalBoundaryCarrier_distinct_sameSignHorizontal_contradiction R F e heF hsep dB hcolor hBsep hl hblocks hxsign hyA hyB

/--
[fkRectCanonicalBoundaryCarrier_distinct_sameSignDiagonal_contradiction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryPotentialContradiction.lean)
-/
@[path]
private lemma fkRectCanonicalBoundaryCarrier_distinct_sameSignDiagonal_contradiction_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
  {dB : FKMedialDart R.medialTorus}
  {l : List FKRectIntegralSquareDart}
-- given
  (heF : e ∉ F)
  (hsep : ¬ (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F))).Reachable (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) (fkMedialEastDart (fkRectMedialVertexOfEdge R e)))
  (hcolor : fkMedialCheckerColor dB = fkMedialCheckerColor (fkMedialWestDart (fkRectMedialVertexOfEdge R e)))
  (hBsep : ¬ (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F))).Reachable (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) dB)
  (hl : FKRectIntegralSquareDartPath (fkRectRefinedPrimalEdgeStart R e) (fkRectRefinedPrimalEdgeEnd R e) l)
  (hblocks : FKRectRefinedOpenEdgeBlocks R F l)
  (hxsign : let omega := fkRectConfigurationOfEdges R F let dA := fkMedialWestDart (fkRectMedialVertexOfEdge R e) let A := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dA let B := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dB 0 < (A.map StatMech.Onsager.ons_xWrapSign).sum * (B.map StatMech.Onsager.ons_xWrapSign).sum)
  (hdiagA : let omega := fkRectConfigurationOfEdges R F let dA := fkMedialWestDart (fkRectMedialVertexOfEdge R e) let A := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dA (A.map StatMech.Onsager.ons_yWrapSign).sum = (A.map StatMech.Onsager.ons_xWrapSign).sum)
  (hdiagB : let omega := fkRectConfigurationOfEdges R F let B := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dB (B.map StatMech.Onsager.ons_yWrapSign).sum = (B.map StatMech.Onsager.ons_xWrapSign).sum) :
-- imply
  False := by
-- proof
  apply StatMech.FrontierD.fkRectCanonicalBoundaryCarrier_distinct_sameSignDiagonal_contradiction R F e heF hsep dB hcolor hBsep hl hblocks hxsign hdiagA hdiagB

/--
[fkRectCanonicalBoundaryCarrier_distinct_sameSignFKHorizontal_contradiction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryPotentialContradiction.lean)
-/
@[path]
private lemma fkRectCanonicalBoundaryCarrier_distinct_sameSignFKHorizontal_contradiction_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
  {dB : FKMedialDart R.medialTorus}
  {l : List FKRectIntegralSquareDart}
-- given
  (heF : e ∉ F)
  (hsep : ¬ (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F))).Reachable (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) (fkMedialEastDart (fkRectMedialVertexOfEdge R e)))
  (hcolor : fkMedialCheckerColor dB = fkMedialCheckerColor (fkMedialWestDart (fkRectMedialVertexOfEdge R e)))
  (hBsep : ¬ (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F))).Reachable (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) dB)
  (hl : FKRectIntegralSquareDartPath (fkRectRefinedPrimalEdgeStart R e) (fkRectRefinedPrimalEdgeEnd R e) l)
  (hblocks : FKRectRefinedOpenEdgeBlocks R F l)
  (hxsign : let omega := fkRectConfigurationOfEdges R F let dA := fkMedialWestDart (fkRectMedialVertexOfEdge R e) 0 < (fkRectWalkWinding R (fkRectMedialBoundaryPrimalOrbitWalk R omega dA)).1 * (fkRectWalkWinding R (fkRectMedialBoundaryPrimalOrbitWalk R omega dB)).1)
  (hyA : let omega := fkRectConfigurationOfEdges R F let dA := fkMedialWestDart (fkRectMedialVertexOfEdge R e) (fkRectWalkWinding R (fkRectMedialBoundaryPrimalOrbitWalk R omega dA)).2 = 0)
  (hyB : let omega := fkRectConfigurationOfEdges R F (fkRectWalkWinding R (fkRectMedialBoundaryPrimalOrbitWalk R omega dB)).2 = 0) :
-- imply
  False := by
-- proof
  apply StatMech.FrontierD.fkRectCanonicalBoundaryCarrier_distinct_sameSignFKHorizontal_contradiction R F e heF hsep dB hcolor hBsep hl hblocks hxsign hyA hyB

/--
[fkRectCanonicalBoundaryCarrier_distinct_equalWinding_contradiction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryPotentialContradiction.lean)
-/
@[path]
private lemma fkRectCanonicalBoundaryCarrier_distinct_equalWinding_contradiction_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
  {dB : FKMedialDart R.medialTorus}
  {l : List FKRectIntegralSquareDart}
-- given
  (heF : e ∉ F)
  (hsep : ¬ (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F))).Reachable (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) (fkMedialEastDart (fkRectMedialVertexOfEdge R e)))
  (hcolor : fkMedialCheckerColor dB = fkMedialCheckerColor (fkMedialWestDart (fkRectMedialVertexOfEdge R e)))
  (hBsep : ¬ (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F))).Reachable (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) dB)
  (hl : FKRectIntegralSquareDartPath (fkRectRefinedPrimalEdgeStart R e) (fkRectRefinedPrimalEdgeEnd R e) l)
  (hblocks : FKRectRefinedOpenEdgeBlocks R F l)
  (hwinding : let omega := fkRectConfigurationOfEdges R F let dA := fkMedialWestDart (fkRectMedialVertexOfEdge R e) fkRectWalkWinding R (fkRectMedialBoundaryPrimalOrbitWalk R omega dA) = fkRectWalkWinding R (fkRectMedialBoundaryPrimalOrbitWalk R omega dB)) :
-- imply
  False := by
-- proof
  apply StatMech.FrontierD.fkRectCanonicalBoundaryCarrier_distinct_equalWinding_contradiction R F e heF hsep dB hcolor hBsep hl hblocks hwinding


-- created on 2026-10-23
