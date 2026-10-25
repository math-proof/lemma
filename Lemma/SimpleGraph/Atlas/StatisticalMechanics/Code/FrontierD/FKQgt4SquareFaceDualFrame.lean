import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareFaceDualFrame.Part2
open Set SimpleGraph StatMech StatMech.FrontierD


/--
[fci_faceEdgeEquiv_symm_mk_of_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareFaceDualFrame.lean)
-/
@[path]
private lemma fci_faceEdgeEquiv_symm_mk_of_adj_eq
  {x y : Site 2}
-- given
  (hxy : (hypercubicLattice 2).Adj x y) :
-- imply
  fci_faceEdgeEquiv.symm s(x, y) = flankFaces x y := by
-- proof
  apply StatMech.FrontierD.fci_faceEdgeEquiv_symm_mk_of_adj hxy

/--
[inverseFaceDualConfig_eq_faceDual_doubleDualShift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareFaceDualFrame.lean)
-/
@[path]
private lemma inverseFaceDualConfig_eq_faceDual_doubleDualShift_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {x y : Site 2}
-- given
  (hxy : (hypercubicLattice 2).Adj x y) :
-- imply
  inverseFaceDualConfig omega s(x, y) = fci_faceDualConfig omega s(phb_doubleDualShift x, phb_doubleDualShift y) := by
-- proof
  apply StatMech.FrontierD.inverseFaceDualConfig_eq_faceDual_doubleDualShift omega hxy

/--
[fciFrameTranslation_inv_smul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareFaceDualFrame.lean)
-/
@[path]
private lemma fciFrameTranslation_inv_smul_eq
  {x : Site 2} :
-- imply
  fciFrameTranslation⁻¹ • x = phb_doubleDualShift x := by
-- proof
  apply StatMech.FrontierD.fciFrameTranslation_inv_smul x

/--
[inverseFaceDualConfig_eq_shift_faceDual_of_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareFaceDualFrame.lean)
-/
@[path]
private lemma inverseFaceDualConfig_eq_shift_faceDual_of_adj_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {x y : Site 2}
-- given
  (hxy : (hypercubicLattice 2).Adj x y) :
-- imply
  inverseFaceDualConfig omega s(x, y) = ConfigSpace.shift fciFrameTranslation (fci_faceDualConfig omega) s(x, y) := by
-- proof
  apply StatMech.FrontierD.inverseFaceDualConfig_eq_shift_faceDual_of_adj omega hxy

/--
[openSubgraph_inverseFaceDual_eq_shift_faceDual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareFaceDualFrame.lean)
-/
@[path]
private lemma openSubgraph_inverseFaceDual_eq_shift_faceDual_eq
  {omega : ConfigSpace (Sym2 (Site 2))} :
-- imply
  openSubgraph 2 (inverseFaceDualConfig omega) = openSubgraph 2 (ConfigSpace.shift fciFrameTranslation (fci_faceDualConfig omega)) := by
-- proof
  apply StatMech.FrontierD.openSubgraph_inverseFaceDual_eq_shift_faceDual omega

/--
[inverseFaceDual_hasInfiniteCluster_iff_faceDual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareFaceDualFrame.lean)
-/
@[path]
private lemma inverseFaceDual_hasInfiniteCluster_iff_faceDual_eq
  {omega : ConfigSpace (Sym2 (Site 2))} :
-- imply
  square.HasInfiniteCluster (inverseFaceDualConfig omega) ↔ square.HasInfiniteCluster (fci_faceDualConfig omega) := by
-- proof
  apply StatMech.FrontierD.inverseFaceDual_hasInfiniteCluster_iff_faceDual omega


-- created on 2026-10-23
