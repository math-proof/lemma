import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.euceuler
open Finset StatMech StatMech.Euc


/--
[euc_cellVerts_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/euceuler.lean)
-/
@[path]
private lemma euc_cellVerts_card_eq
  {c : Cell} :
-- imply
  (cellVerts c).card = 4 := by
-- proof
  apply StatMech.Euc.euc_cellVerts_card c

/--
[euc_cellEdges_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/euceuler.lean)
-/
@[path]
private lemma euc_cellEdges_card_eq
  {c : Cell} :
-- imply
  (cellEdges c).card = 4 := by
-- proof
  apply StatMech.Euc.euc_cellEdges_card c

/--
[euc_chi_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/euceuler.lean)
-/
@[path]
private lemma euc_chi_singleton_eq
  {c : Cell} :
-- imply
  regChi {c} = 1 := by
-- proof
  apply StatMech.Euc.euc_chi_singleton c

/--
[euc_regVerts_insert](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/euceuler.lean)
-/
@[path]
private lemma euc_regVerts_insert_eq
  {c : Cell}
  {K : Finset Cell} :
-- imply
  regVerts (insert c K) = cellVerts c ∪ regVerts K := by
-- proof
  apply StatMech.Euc.euc_regVerts_insert c K

/--
[euc_regEdges_insert](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/euceuler.lean)
-/
@[path]
private lemma euc_regEdges_insert_eq
  {c : Cell}
  {K : Finset Cell} :
-- imply
  regEdges (insert c K) = cellEdges c ∪ regEdges K := by
-- proof
  apply StatMech.Euc.euc_regEdges_insert c K

/--
[euc_regVerts_card_insert](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/euceuler.lean)
-/
@[path]
private lemma euc_regVerts_card_insert_eq
  {c : Cell}
  {K : Finset Cell} :
-- imply
  (regVerts (insert c K)).card = newVerts c K + (regVerts K).card := by
-- proof
  apply StatMech.Euc.euc_regVerts_card_insert c K

/--
[euc_regEdges_card_insert](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/euceuler.lean)
-/
@[path]
private lemma euc_regEdges_card_insert_eq
  {c : Cell}
  {K : Finset Cell} :
-- imply
  (regEdges (insert c K)).card = newEdges c K + (regEdges K).card := by
-- proof
  apply StatMech.Euc.euc_regEdges_card_insert c K

/--
[euc_chi_insert](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/euceuler.lean)
-/
@[path]
private lemma euc_chi_insert_eq
  {c : Cell}
  {K : Finset Cell}
-- given
  (hc : c ∉ K) :
-- imply
  regChi (insert c K) = regChi K + ((newVerts c K : ℤ) - (newEdges c K : ℤ) + 1) := by
-- proof
  apply StatMech.Euc.euc_chi_insert c K hc

/--
[euc_chi_attach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/euceuler.lean)
-/
@[path]
private lemma euc_chi_attach_eq
  {c : Cell}
  {K : Finset Cell}
-- given
  (hc : c ∉ K)
  (harc : newEdges c K = newVerts c K + 1) :
-- imply
  regChi (insert c K) = regChi K := by
-- proof
  apply StatMech.Euc.euc_chi_attach c K hc harc

/--
[euc_chi_induction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/euceuler.lean)
-/
@[path]
private lemma euc_chi_induction_eq
  {K : Finset Cell}
-- given
  (hK : EucBuildable K) :
-- imply
  regChi K = 1 := by
-- proof
  apply StatMech.Euc.euc_chi_induction hK

/--
[euc_buildable_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/euceuler.lean)
-/
@[path]
private lemma euc_buildable_nonempty_eq
  {K : Finset Cell}
-- given
  (hK : EucBuildable K) :
-- imply
  K.Nonempty := by
-- proof
  apply StatMech.Euc.euc_buildable_nonempty hK

/--
[euc_chi_domino](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/euceuler.lean)
-/
@[path]
private lemma euc_chi_domino_eq :
-- imply
  regChi {((0 : ℤ), (0 : ℤ)), (1, 0)} = 1 := by
-- proof
  apply StatMech.Euc.euc_chi_domino

/--
[euc_chi_box2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/euceuler.lean)
-/
@[path]
private lemma euc_chi_box2_eq :
-- imply
  regChi {((0 : ℤ), (0 : ℤ)), (1, 0), (0, 1), (1, 1)} = 1 := by
-- proof
  apply StatMech.Euc.euc_chi_box2

/--
[euc_chi_Ltromino](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/euceuler.lean)
-/
@[path]
private lemma euc_chi_Ltromino_eq :
-- imply
  regChi {((0 : ℤ), (0 : ℤ)), (1, 0), (0, 1)} = 1 := by
-- proof
  apply StatMech.Euc.euc_chi_Ltromino

/--
[euc_chi_holeyRing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/euceuler.lean)
-/
@[path]
private lemma euc_chi_holeyRing_eq :
-- imply
  regChi ({((0:ℤ),(0:ℤ)),(1,0),(2,0),(0,1),(2,1),(0,2),(1,2),(2,2)} : Finset Cell) = 0 := by
-- proof
  apply StatMech.Euc.euc_chi_holeyRing

/--
[euc_buildable_domino](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/euceuler.lean)
-/
@[path]
private lemma euc_buildable_domino_eq :
-- imply
  EucBuildable ({((0:ℤ),(0:ℤ)), (1,0)} : Finset Cell) := by
-- proof
  apply StatMech.Euc.euc_buildable_domino

/--
[euc_buildable_Ltromino](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/euceuler.lean)
-/
@[path]
private lemma euc_buildable_Ltromino_eq :
-- imply
  EucBuildable ({((0:ℤ),(0:ℤ)), (1,0), (0,1)} : Finset Cell) := by
-- proof
  apply StatMech.Euc.euc_buildable_Ltromino


-- created on 2026-10-23
