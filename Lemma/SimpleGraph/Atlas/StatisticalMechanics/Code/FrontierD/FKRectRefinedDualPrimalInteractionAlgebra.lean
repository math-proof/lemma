import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedDualPrimalInteractionAlgebra.Part2
open StatMech StatMech.FrontierD


/--
[fkRectIntegralSquareDartList_translate_comp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedDualPrimalInteractionAlgebra.lean)
-/
@[path]
private lemma fkRectIntegralSquareDartList_translate_comp_eq
  {l : List FKRectIntegralSquareDart}
  {a b : Int × Int} :
-- imply
  ((l.map (fkRectIntegralSquareDartTranslate a)).map (fkRectIntegralSquareDartTranslate b)) = l.map (fkRectIntegralSquareDartTranslate (a.1 + b.1, a.2 + b.2)) := by
-- proof
  apply StatMech.FrontierD.fkRectIntegralSquareDartList_translate_comp l a b

/--
[fkRectRefinedDeckTranslation_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedDualPrimalInteractionAlgebra.lean)
-/
@[path]
private lemma fkRectRefinedDeckTranslation_add_eq
  {R : FKRectTorus}
  {u v : Int × Int} :
-- imply
  ((fkRectRefinedDeckTranslation R u).1 + (fkRectRefinedDeckTranslation R v).1, (fkRectRefinedDeckTranslation R u).2 + (fkRectRefinedDeckTranslation R v).2) = fkRectRefinedDeckTranslation R (u.1 + v.1, u.2 + v.2) := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedDeckTranslation_add R u v

/--
[fkRectNatScale_refinedDeckTranslation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedDualPrimalInteractionAlgebra.lean)
-/
@[path]
private lemma fkRectNatScale_refinedDeckTranslation_eq
  {R : FKRectTorus}
  {n : Nat}
  {u : Int × Int} :
-- imply
  fkRectNatScale n (fkRectRefinedDeckTranslation R u) = fkRectRefinedDeckTranslation R ((n : Int) * u.1, (n : Int) * u.2) := by
-- proof
  apply StatMech.FrontierD.fkRectNatScale_refinedDeckTranslation R n u

/--
[fkRectRefinedRawInteraction_reverse_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedDualPrimalInteractionAlgebra.lean)
-/
@[path]
private lemma fkRectRefinedRawInteraction_reverse_left_eq
  {L : Nat}
  [Fact (8 < L)]
  {a b : List (ons_Dart L)} :
-- imply
  fkRectRefinedRawInteraction (a.reverse.map (ons_dartRev L)) b = -fkRectRefinedRawInteraction a b := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedRawInteraction_reverse_left a b

/--
[fkRectRefinedRawInteraction_integralReverse_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedDualPrimalInteractionAlgebra.lean)
-/
@[path]
private lemma fkRectRefinedRawInteraction_integralReverse_left_eq
  {L : Nat}
  [Fact (8 < L)]
  {a : List FKRectIntegralSquareDart}
  {b : List (ons_Dart L)} :
-- imply
  fkRectRefinedRawInteraction ((fkRectIntegralSquareDartListReverse a).map (fkRectIntegralSquareDartMod L)) b = -fkRectRefinedRawInteraction (a.map (fkRectIntegralSquareDartMod L)) b := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedRawInteraction_integralReverse_left a b

/--
[FKRectRefinedOpenEdgeBlocks.translated_interaction_eq_zero_of_dualEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedDualPrimalInteractionAlgebra.lean)
-/
@[path]
private lemma translated_interaction_eq_zero_of_dualEdge_eq
  {L : Nat}
  [Fact (8 < L)]
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {k : List FKRectIntegralSquareDart}
  {d : R.EdgeIndex}
  {a b : Int × Int}
-- given
  (hk : FKRectRefinedOpenEdgeBlocks R F k)
  (hlocal : ∀ (e : R.EdgeIndex), e ∈ F → ∀ v : Int × Int, fkRectRefinedRawInteraction (((fkRectRefinedDualEdgeDarts R d).map (fkRectIntegralSquareDartTranslate (fkRectRefinedDeckTranslation R a))).map (fkRectIntegralSquareDartMod L)) (((fkRectRefinedPrimalEdgeDarts R e).map (fkRectIntegralSquareDartTranslate (fkRectRefinedDeckTranslation R v))).map (fkRectIntegralSquareDartMod L)) = 0) :
-- imply
  fkRectRefinedRawInteraction (((fkRectRefinedDualEdgeDarts R d).map (fkRectIntegralSquareDartTranslate (fkRectRefinedDeckTranslation R a))).map (fkRectIntegralSquareDartMod L)) ((k.map (fkRectIntegralSquareDartTranslate (fkRectRefinedDeckTranslation R b))).map (fkRectIntegralSquareDartMod L)) = 0 := by
-- proof
  apply StatMech.FrontierD.FKRectRefinedOpenEdgeBlocks.translated_interaction_eq_zero_of_dualEdge R F hk d a b hlocal

/--
[FKRectRefinedDualOpenEdgeBlocks.translated_interaction_eq_zero_of_edgeBlocks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedDualPrimalInteractionAlgebra.lean)
-/
@[path]
private lemma translated_interaction_eq_zero_of_edgeBlocks_eq
  {L : Nat}
  [Fact (8 < L)]
  {R : FKRectTorus}
  {omega : R.Configuration}
  {F : Finset R.EdgeIndex}
  {l k : List FKRectIntegralSquareDart}
  {a b : Int × Int}
-- given
  (hl : FKRectRefinedDualOpenEdgeBlocks R omega l)
  (hk : FKRectRefinedOpenEdgeBlocks R F k)
  (hlocal : ∀ (d e : R.EdgeIndex), fkRectDualConfigurationEquiv R omega d = true → e ∈ F → ∀ (u v : Int × Int), fkRectRefinedRawInteraction (((fkRectRefinedDualEdgeDarts R d).map (fkRectIntegralSquareDartTranslate (fkRectRefinedDeckTranslation R u))).map (fkRectIntegralSquareDartMod L)) (((fkRectRefinedPrimalEdgeDarts R e).map (fkRectIntegralSquareDartTranslate (fkRectRefinedDeckTranslation R v))).map (fkRectIntegralSquareDartMod L)) = 0) :
-- imply
  fkRectRefinedRawInteraction ((l.map (fkRectIntegralSquareDartTranslate (fkRectRefinedDeckTranslation R a))).map (fkRectIntegralSquareDartMod L)) ((k.map (fkRectIntegralSquareDartTranslate (fkRectRefinedDeckTranslation R b))).map (fkRectIntegralSquareDartMod L)) = 0 := by
-- proof
  apply StatMech.FrontierD.FKRectRefinedDualOpenEdgeBlocks.translated_interaction_eq_zero_of_edgeBlocks R omega F hl hk a b hlocal

/--
[FKRectRefinedDualOpenEdgeBlocks.repeated_interaction_eq_zero_of_edgeBlocks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedDualPrimalInteractionAlgebra.lean)
-/
@[path]
private lemma repeated_interaction_eq_zero_of_edgeBlocks_eq
  {L : Nat}
  [Fact (8 < L)]
  {R : FKRectTorus}
  {omega : R.Configuration}
  {F : Finset R.EdgeIndex}
  {l k : List FKRectIntegralSquareDart}
  {w z : Int × Int}
  {n m : Nat}
-- given
  (hl : FKRectRefinedDualOpenEdgeBlocks R omega l)
  (hk : FKRectRefinedOpenEdgeBlocks R F k)
  (hlocal : ∀ (d e : R.EdgeIndex), fkRectDualConfigurationEquiv R omega d = true → e ∈ F → ∀ (u v : Int × Int), fkRectRefinedRawInteraction (((fkRectRefinedDualEdgeDarts R d).map (fkRectIntegralSquareDartTranslate (fkRectRefinedDeckTranslation R u))).map (fkRectIntegralSquareDartMod L)) (((fkRectRefinedPrimalEdgeDarts R e).map (fkRectIntegralSquareDartTranslate (fkRectRefinedDeckTranslation R v))).map (fkRectIntegralSquareDartMod L)) = 0) :
-- imply
  fkRectRefinedRawInteraction ((fkRectRepeatTranslatedDartPath l (fkRectRefinedDeckTranslation R w) n).map (fkRectIntegralSquareDartMod L)) ((fkRectRepeatTranslatedDartPath k (fkRectRefinedDeckTranslation R z) m).map (fkRectIntegralSquareDartMod L)) = 0 := by
-- proof
  apply StatMech.FrontierD.FKRectRefinedDualOpenEdgeBlocks.repeated_interaction_eq_zero_of_edgeBlocks R omega F hl hk w z n m hlocal


-- created on 2026-10-23
