import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopPlusDualRectangle.Part4
open Finset SimpleGraph Set StatMech StatMech.Onsager


/--
[ons_flankFacesSym_mem_plusDualFaceEdgeSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusDualRectangle.lean)
-/
@[path]
private lemma ons_flankFacesSym_mem_plusDualFaceEdgeSet_eq
  {n : Nat}
  {edge : Sym2 (Site 2)}
-- given
  (hedge : edge ∈ bondFinsetTouch 2 n) :
-- imply
  flankFacesSym edge ∈ ons_plusDualFaceEdgeSet n := by
-- proof
  apply StatMech.Onsager.ons_flankFacesSym_mem_plusDualFaceEdgeSet n hedge

/--
[ons_symPrimalSym_mem_bondFinsetTouch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusDualRectangle.lean)
-/
@[path]
private lemma ons_symPrimalSym_mem_bondFinsetTouch_eq
  {n : Nat}
  {edge : Sym2 (Site 2)}
-- given
  (hedge : edge ∈ ons_plusDualFaceEdgeSet n) :
-- imply
  symPrimalSym edge ∈ bondFinsetTouch 2 n := by
-- proof
  apply StatMech.Onsager.ons_symPrimalSym_mem_bondFinsetTouch n hedge

/--
[ons_plusDualFaceEquivRect_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusDualRectangle.lean)
-/
@[path]
private lemma ons_plusDualFaceEquivRect_adj_eq
  {n : Nat}
  {f g : ons_PlusDualFaceVertex n} :
-- imply
  (ons_plusDualFaceGraph n).Adj f g ↔ (ons_rectDualGraph (2 * n + 1) (2 * n + 1)).Adj (ons_plusDualFaceEquivRect n f) (ons_plusDualFaceEquivRect n g) := by
-- proof
  apply StatMech.Onsager.ons_plusDualFaceEquivRect_adj n f g

/--
[ons_plusDualFaceEdgeLift_map_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusDualRectangle.lean)
-/
@[path]
private lemma ons_plusDualFaceEdgeLift_map_val_eq
  {n : Nat}
-- given
  (edge : {edge // edge ∈ ons_plusDualFaceEdgeSet n}) :
-- imply
  Sym2.map Subtype.val (ons_plusDualFaceEdgeLift n edge) = edge.1 := by
-- proof
  apply StatMech.Onsager.ons_plusDualFaceEdgeLift_map_val n edge

/--
[ons_plusDualFaceEdgeLift_mem_edgeFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusDualRectangle.lean)
-/
@[path]
private lemma ons_plusDualFaceEdgeLift_mem_edgeFinset_eq
  {n : Nat}
-- given
  (edge : {edge // edge ∈ ons_plusDualFaceEdgeSet n}) :
-- imply
  ons_plusDualFaceEdgeLift n edge ∈ (ons_plusDualFaceGraph n).edgeFinset := by
-- proof
  apply StatMech.Onsager.ons_plusDualFaceEdgeLift_mem_edgeFinset n edge

/--
[ons_plusDualContour_subset_plusDualFaceEdgeSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusDualRectangle.lean)
-/
@[path]
private lemma ons_plusDualContour_subset_plusDualFaceEdgeSet_eq
  {n : Nat}
-- given
  (tau : {x // x ∈ box 2 n} -> Bool) :
-- imply
  ∀ edge ∈ ons_plusDualContour n tau, edge ∈ ons_plusDualFaceEdgeSet n := by
-- proof
  apply StatMech.Onsager.ons_plusDualContour_subset_plusDualFaceEdgeSet n tau


-- created on 2026-10-23
