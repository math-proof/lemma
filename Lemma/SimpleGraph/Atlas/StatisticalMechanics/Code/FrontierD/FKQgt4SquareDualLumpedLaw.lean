import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKQgt4SquareDualLumpedLaw
open Finset Set SimpleGraph StatMech StatMech.FrontierD


/--
[pfdEdgeComplement_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareDualLumpedLaw.lean)
-/
@[path]
private lemma pfdEdgeComplement_apply_eq
  {P : PlanarZ2Subgraph}
  {omega : ConfigSpace P.G.edgeSet}
  {e : P.G.edgeSet} :
-- imply
  pfdEdgeComplement P omega e = !(omega e) := by
-- proof
  apply StatMech.FrontierD.pfdEdgeComplement_apply P omega e

/--
[pfdEdgeComplement_symm_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareDualLumpedLaw.lean)
-/
@[path]
private lemma pfdEdgeComplement_symm_apply_eq
  {P : PlanarZ2Subgraph}
  {omega : ConfigSpace P.G.edgeSet}
  {e : P.G.edgeSet} :
-- imply
  (pfdEdgeComplement P).symm omega e = !(omega e) := by
-- proof
  apply StatMech.FrontierD.pfdEdgeComplement_symm_apply P omega e

/--
[pfdEdgeComplement_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareDualLumpedLaw.lean)
-/
@[path]
private lemma pfdEdgeComplement_involutive_eq
  {P : PlanarZ2Subgraph}
  {omega : ConfigSpace P.G.edgeSet} :
-- imply
  pfdEdgeComplement P (pfdEdgeComplement P omega) = omega := by
-- proof
  apply StatMech.FrontierD.pfdEdgeComplement_involutive P omega

/--
[pfdDualEdgeProduct_eq_indexed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareDualLumpedLaw.lean)
-/
@[path]
private lemma pfdDualEdgeProduct_eq_indexed_eq
  {P : PlanarZ2Subgraph}
  {p : Real}
  {omega : ConfigSpace (Sym2 P.V)} :
-- imply
  edgeProductCount p P.G.edgeFinset.card (P.G.edgeFinset.card - (openSub P.G omega).edgeSet.ncard) = indexedBernoulliWeight p (fun e : kwg_Edge P => !(omega e.1)) := by
-- proof
  apply StatMech.FrontierD.pfdDualEdgeProduct_eq_indexed P p omega

/--
[pfdClosedDual_eq_openSub_indexedSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareDualLumpedLaw.lean)
-/
@[path]
private lemma pfdClosedDual_eq_openSub_indexedSupport_eq
  {P : PlanarZ2Subgraph}
  {omega : ConfigSpace (Sym2 P.V)} :
-- imply
  pfdClosedDual P (openSub P.G omega) = openSub (pfdClosedDual P ⊥) (extendActive (pfdClosedDual P ⊥) (pfdIndexedSupportActive P (fun e : kwg_Edge P => !(omega e.1)))) := by
-- proof
  apply StatMech.FrontierD.pfdClosedDual_eq_openSub_indexedSupport P omega

/--
[pfdDualWeight_eq_indexedSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareDualLumpedLaw.lean)
-/
@[path]
private lemma pfdDualWeight_eq_indexedSupport_eq
  {P : PlanarZ2Subgraph}
  {p q : Real}
  {omega : ConfigSpace (Sym2 P.V)} :
-- imply
  pfdDualWeight P p q (openSub P.G omega) = indexedBernoulliWeight p (fun e : kwg_Edge P => !(omega e.1)) * q ^ (numClustersBC (pfdClosedDual P ⊥) ⊥ (extendActive (pfdClosedDual P ⊥) (pfdIndexedSupportActive P (fun e : kwg_Edge P => !(omega e.1))))) := by
-- proof
  apply StatMech.FrontierD.pfdDualWeight_eq_indexedSupport P p q omega

/--
[fkSquareDualLumpedParam_compatible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareDualLumpedLaw.lean)
-/
@[path]
private lemma fkSquareDualLumpedParam_compatible_eq
  {N m : Nat}
  {p : Real} :
-- imply
  ocd_ParamCompatible (fkSquareBox_innerFaceMap N m) (fun _ => p) (fkSquareDualLumpedParam N m p) := by
-- proof
  apply StatMech.FrontierD.fkSquareDualLumpedParam_compatible N m p

/--
[fkSquareDualLumpedParam_eq_effective_on_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareDualLumpedLaw.lean)
-/
@[path]
private lemma fkSquareDualLumpedParam_eq_effective_on_edge_eq
  {N m : Nat}
  {p : Real}
  {a : Sym2 (kwg_Face (fkSquareBoxPlanar m))}
-- given
  (hNm : N < m)
  (ha : a ∈ (fkSquareBoxFullDualGraph m).edgeSet) :
-- imply
  fkSquareDualLumpedParam N m p a = indexedEffectiveParam (kwg_dualEnds (fkSquareBoxPlanar m)) p a := by
-- proof
  apply StatMech.FrontierD.fkSquareDualLumpedParam_eq_effective_on_edge hNm p ha

/--
[fkSquareDualLumpedParam_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareDualLumpedLaw.lean)
-/
@[path]
private lemma fkSquareDualLumpedParam_pos_eq
  {N m : Nat}
  {p : Real}
  {a : Sym2 (kwg_Face (fkSquareBoxPlanar m))}
-- given
  (hNm : N < m)
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  0 < fkSquareDualLumpedParam N m p a := by
-- proof
  apply StatMech.FrontierD.fkSquareDualLumpedParam_pos hNm hp hp1 a

/--
[fkSquareDualLumpedParam_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareDualLumpedLaw.lean)
-/
@[path]
private lemma fkSquareDualLumpedParam_lt_one_eq
  {N m : Nat}
  {p : Real}
  {a : Sym2 (kwg_Face (fkSquareBoxPlanar m))}
-- given
  (hNm : N < m)
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  fkSquareDualLumpedParam N m p a < 1 := by
-- proof
  apply StatMech.FrontierD.fkSquareDualLumpedParam_lt_one hNm hp hp1 a

/--
[pfdIndexedWeight_lumping](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareDualLumpedLaw.lean)
-/
@[path]
private lemma pfdIndexedWeight_lumping_eq
  {N m : Nat}
  {p q : Real}
  {F : ConfigSpace (fkSquareBoxFullDualGraph m).edgeSet → Real}
-- given
  (hNm : N < m) :
-- imply
  (∑ eta : ConfigSpace (fkSquareBoxPlanar m).G.edgeSet, indexedBernoulliWeight p eta * (F (pfdIndexedSupportActive (fkSquareBoxPlanar m) eta) * q ^ numClustersBC (fkSquareBoxFullDualGraph m) ⊥ (extendActive (fkSquareBoxFullDualGraph m) (pfdIndexedSupportActive (fkSquareBoxPlanar m) eta)))) = ∑ rho : ConfigSpace (fkSquareBoxFullDualGraph m).edgeSet, F rho * activeBCWeight (fkSquareBoxFullDualGraph m) ⊥ (fkSquareDualLumpedParam N m p) q rho := by
-- proof
  apply StatMech.FrontierD.pfdIndexedWeight_lumping hNm p q F

/--
[fkSquare_pfdDualNumer_eq_lumped](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareDualLumpedLaw.lean)
-/
@[path]
private lemma fkSquare_pfdDualNumer_eq_lumped_eq
  {N m : Nat}
  {p q : Real}
  {F : ConfigSpace (fkSquareBoxFullDualGraph m).edgeSet → Real}
-- given
  (hNm : N < m) :
-- imply
  (∑ omega : ConfigSpace (Sym2 (FK.boxVerts 2 m)), F (fkSquarePfdSupport m omega) * pfdDualWeight (fkSquareBoxPlanar m) p q (openSub (FK.boxGraph 2 m) omega)) = 2 ^ ecz_NE (FK.boxGraph 2 m) * ∑ rho : ConfigSpace (fkSquareBoxFullDualGraph m).edgeSet, F rho * activeBCWeight (fkSquareBoxFullDualGraph m) ⊥ (fkSquareDualLumpedParam N m p) q rho := by
-- proof
  apply StatMech.FrontierD.fkSquare_pfdDualNumer_eq_lumped hNm p q F

/--
[fkSquare_pfdDualZ_eq_lumped](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareDualLumpedLaw.lean)
-/
@[path]
private lemma fkSquare_pfdDualZ_eq_lumped_eq
  {N m : Nat}
  {p q : Real}
-- given
  (hNm : N < m) :
-- imply
  pfdDualZ (fkSquareBoxPlanar m) p q = 2 ^ ecz_NE (FK.boxGraph 2 m) * activeBCZ (fkSquareBoxFullDualGraph m) ⊥ (fkSquareDualLumpedParam N m p) q := by
-- proof
  apply StatMech.FrontierD.fkSquare_pfdDualZ_eq_lumped hNm p q

/--
[fkSquare_pfdDualMean_eq_lumped](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareDualLumpedLaw.lean)
-/
@[path]
private lemma fkSquare_pfdDualMean_eq_lumped_eq
  {N m : Nat}
  {p q : Real}
  {F : ConfigSpace (fkSquareBoxFullDualGraph m).edgeSet → Real}
-- given
  (hNm : N < m)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  (∑ omega : ConfigSpace (Sym2 (FK.boxVerts 2 m)), F (fkSquarePfdSupport m omega) * pfdDualProb (fkSquareBoxPlanar m) p q omega) = ∑ rho : ConfigSpace (fkSquareBoxFullDualGraph m).edgeSet, F rho * activeBCProb (fkSquareBoxFullDualGraph m) ⊥ (fkSquareDualLumpedParam N m p) q rho := by
-- proof
  apply StatMech.FrontierD.fkSquare_pfdDualMean_eq_lumped hNm hp hp1 hq F


-- created on 2026-10-23
