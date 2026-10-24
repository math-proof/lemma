import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKQgt4SquarePeriodicDualCoordinates
open Set SimpleGraph StatMech StatMech.FrontierD


/--
[sharedPrimalEdge_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquarePeriodicDualCoordinates.lean)
-/
@[path]
private lemma sharedPrimalEdge_add_eq
  {z f g : Site 2} :
-- imply
  sharedPrimalEdge (f + z) (g + z) = Sym2.map (siteTranslate z) (sharedPrimalEdge f g) := by
-- proof
  apply StatMech.FrontierD.sharedPrimalEdge_add z f g

/--
[fci_faceEdgeEquiv_mem_edgeSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquarePeriodicDualCoordinates.lean)
-/
@[path]
private lemma fci_faceEdgeEquiv_mem_edgeSet_eq
  {e : Sym2 (Site 2)} :
-- imply
  e ∈ (hypercubicLattice 2).edgeSet ↔ fci_faceEdgeEquiv e ∈ (hypercubicLattice 2).edgeSet := by
-- proof
  apply StatMech.FrontierD.fci_faceEdgeEquiv_mem_edgeSet e

/--
[fci_faceEdgeEquiv_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquarePeriodicDualCoordinates.lean)
-/
@[path]
private lemma fci_faceEdgeEquiv_shift_eq
  {z : Site 2}
  {e : Sym2 (Site 2)} :
-- imply
  fci_faceEdgeEquiv (Sym2.map (siteTranslate z) e) = Sym2.map (siteTranslate z) (fci_faceEdgeEquiv e) := by
-- proof
  apply StatMech.FrontierD.fci_faceEdgeEquiv_shift z e

/--
[dualConfigEquiv_fci_faceEdgeEquiv_eq_inverseFaceDualConfig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquarePeriodicDualCoordinates.lean)
-/
@[path]
private lemma dualConfigEquiv_fci_faceEdgeEquiv_eq_inverseFaceDualConfig_eq :
-- imply
  (dualConfigEquiv fci_faceEdgeEquiv : ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2))) = inverseFaceDualConfig := by
-- proof
  apply StatMech.FrontierD.dualConfigEquiv_fci_faceEdgeEquiv_eq_inverseFaceDualConfig

/--
[dualConfigEquiv_fci_faceEdgeEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquarePeriodicDualCoordinates.lean)
-/
@[path]
private lemma dualConfigEquiv_fci_faceEdgeEquiv_apply_eq
  {omega : ConfigSpace (Sym2 (Site 2))} :
-- imply
  dualConfigEquiv fci_faceEdgeEquiv omega = inverseFaceDualConfig omega := by
-- proof
  apply StatMech.FrontierD.dualConfigEquiv_fci_faceEdgeEquiv_apply omega

/--
[fkSquareBoxPlanar_dualVertex_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquarePeriodicDualCoordinates.lean)
-/
@[path]
private lemma fkSquareBoxPlanar_dualVertex_card_eq
  {n : Nat} :
-- imply
  Nat.card (StatMech.Ising.kwg_Face (fkSquareBoxPlanar n)) = (2 * n) ^ 2 + 1 := by
-- proof
  apply StatMech.FrontierD.fkSquareBoxPlanar_dualVertex_card n

/--
[not_nonempty_faithfulDual_equiv_centeredSquareBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquarePeriodicDualCoordinates.lean)
-/
@[path]
private lemma not_nonempty_faithfulDual_equiv_centeredSquareBox_eq
  {n : Nat}
  {m : Nat}
-- given
  (hn : 0 < n) :
-- imply
  IsEmpty (StatMech.Ising.kwg_Face (fkSquareBoxPlanar n) ≃ StatMech.FK.boxVerts 2 m) := by
-- proof
  apply StatMech.FrontierD.not_nonempty_faithfulDual_equiv_centeredSquareBox hn m


-- created on 2026-10-23
