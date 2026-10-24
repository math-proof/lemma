import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.TriHexBrickDualLumpedLaw
open Finset Set SimpleGraph StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[triHexBrickDualLumpedParam_compatible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickDualLumpedLaw.lean)
-/
@[path]
private lemma triHexBrickDualLumpedParam_compatible_eq
  {N m : Nat}
  {p : Real} :
-- imply
  ocd_ParamCompatible (triHexBrickInnerFaceMap N m) (fun _ => p) (triHexBrickDualLumpedParam N m p) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexBrickDualLumpedParam_compatible N m p

/--
[triHexBrickDualLumpedParam_eq_effective_on_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickDualLumpedLaw.lean)
-/
@[path]
private lemma triHexBrickDualLumpedParam_eq_effective_on_edge_eq
  {N m : Nat}
  {p : Real}
  {a : Sym2 (kwg_Face (triHexPlanarFiniteStarPlanar m))}
-- given
  (hNm : N < m)
  (ha : a ∈ (triHexBrickFullDualGraph m).edgeSet) :
-- imply
  triHexBrickDualLumpedParam N m p a = indexedEffectiveParam (kwg_dualEnds (triHexPlanarFiniteStarPlanar m)) p a := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexBrickDualLumpedParam_eq_effective_on_edge hNm p ha

/--
[triHexBrickDualLumpedParam_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickDualLumpedLaw.lean)
-/
@[path]
private lemma triHexBrickDualLumpedParam_pos_eq
  {N m : Nat}
  {p : Real}
  {a : Sym2 (kwg_Face (triHexPlanarFiniteStarPlanar m))}
-- given
  (hNm : N < m)
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  0 < triHexBrickDualLumpedParam N m p a := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexBrickDualLumpedParam_pos hNm hp hp1 a

/--
[triHexBrickDualLumpedParam_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickDualLumpedLaw.lean)
-/
@[path]
private lemma triHexBrickDualLumpedParam_lt_one_eq
  {N m : Nat}
  {p : Real}
  {a : Sym2 (kwg_Face (triHexPlanarFiniteStarPlanar m))}
-- given
  (hNm : N < m)
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  triHexBrickDualLumpedParam N m p a < 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexBrickDualLumpedParam_lt_one hNm hp hp1 a

/--
[triHexBrick_pfdIndexedWeight_lumping](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickDualLumpedLaw.lean)
-/
@[path]
private lemma triHexBrick_pfdIndexedWeight_lumping_eq
  {N m : Nat}
  {p q : Real}
  {F : ConfigSpace (triHexBrickFullDualGraph m).edgeSet → Real}
-- given
  (hNm : N < m) :
-- imply
  (∑ eta : ConfigSpace (triHexPlanarFiniteStarPlanar m).G.edgeSet, indexedBernoulliWeight p eta * (F (pfdIndexedSupportActive (triHexPlanarFiniteStarPlanar m) eta) * q ^ numClustersBC (triHexBrickFullDualGraph m) ⊥ (extendActive (triHexBrickFullDualGraph m) (pfdIndexedSupportActive (triHexPlanarFiniteStarPlanar m) eta)))) = ∑ rho : ConfigSpace (triHexBrickFullDualGraph m).edgeSet, F rho * activeBCWeight (triHexBrickFullDualGraph m) ⊥ (triHexBrickDualLumpedParam N m p) q rho := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexBrick_pfdIndexedWeight_lumping hNm p q F

/--
[triHexBrick_pfdDualNumer_eq_lumped](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickDualLumpedLaw.lean)
-/
@[path]
private lemma triHexBrick_pfdDualNumer_eq_lumped_eq
  {N m : Nat}
  {p q : Real}
  {F : ConfigSpace (triHexBrickFullDualGraph m).edgeSet → Real}
-- given
  (hNm : N < m) :
-- imply
  (∑ omega : ConfigSpace (Sym2 (triHexPlanarFiniteStarPlanar m).V), F (triHexBrickPfdSupport m omega) * pfdDualWeight (triHexPlanarFiniteStarPlanar m) p q (openSub (triHexPlanarFiniteStarPlanar m).G omega)) = 2 ^ ecz_NE (triHexPlanarFiniteStarPlanar m).G * ∑ rho : ConfigSpace (triHexBrickFullDualGraph m).edgeSet, F rho * activeBCWeight (triHexBrickFullDualGraph m) ⊥ (triHexBrickDualLumpedParam N m p) q rho := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexBrick_pfdDualNumer_eq_lumped hNm p q F

/--
[triHexBrick_pfdDualZ_eq_lumped](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickDualLumpedLaw.lean)
-/
@[path]
private lemma triHexBrick_pfdDualZ_eq_lumped_eq
  {N m : Nat}
  {p q : Real}
-- given
  (hNm : N < m) :
-- imply
  pfdDualZ (triHexPlanarFiniteStarPlanar m) p q = 2 ^ ecz_NE (triHexPlanarFiniteStarPlanar m).G * activeBCZ (triHexBrickFullDualGraph m) ⊥ (triHexBrickDualLumpedParam N m p) q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexBrick_pfdDualZ_eq_lumped hNm p q

/--
[triHexBrick_pfdDualMean_eq_lumped](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickDualLumpedLaw.lean)
-/
@[path]
private lemma triHexBrick_pfdDualMean_eq_lumped_eq
  {N m : Nat}
  {p q : Real}
  {F : ConfigSpace (triHexBrickFullDualGraph m).edgeSet → Real}
-- given
  (hNm : N < m)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  (∑ omega : ConfigSpace (Sym2 (triHexPlanarFiniteStarPlanar m).V), F (triHexBrickPfdSupport m omega) * pfdDualProb (triHexPlanarFiniteStarPlanar m) p q omega) = ∑ rho : ConfigSpace (triHexBrickFullDualGraph m).edgeSet, F rho * activeBCProb (triHexBrickFullDualGraph m) ⊥ (triHexBrickDualLumpedParam N m p) q rho := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexBrick_pfdDualMean_eq_lumped hNm hp hp1 hq F


-- created on 2026-10-23
