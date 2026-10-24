import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedOffset
open StatMech StatMech.FrontierD


/--
[sixVertexCanonicalEvenHalfIndex_quantum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedOffset.lean)
-/
@[path]
private lemma sixVertexCanonicalEvenHalfIndex_quantum_eq
  {s k : Nat}
  {j : Fin ((s + k + 1) + (s + k + 1))} :
-- imply
  sixVertexCentralQuantumNumber (sixVertexCanonicalEvenHalfIndex s k j) = sixVertexCentralQuantumNumber j := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalEvenHalfIndex_quantum s k j

/--
[sixVertexCanonicalEvenChargeOffset_eq_thetaDifference](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedOffset.lean)
-/
@[path]
private lemma sixVertexCanonicalEvenChargeOffset_eq_thetaDifference_eq
  {c : Real}
  {s k : Nat}
  {j : Fin ((s + k + 1) + (s + k + 1))}
-- given
  (hc : 2 < c)
  (hfixed : SixVertexFixedEvenChargePerronBranchWitness c s k (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k)) :
-- imply
  sixVertexCanonicalEvenChargeOffset hc s k j = (∑ l, sixVertexTheta c (sixVertexCanonicalEvenAlignedHalfRoots hc s k j) (sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + k) l)) - ∑ l, sixVertexTheta c (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k j) (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k l) := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalEvenChargeOffset_eq_thetaDifference hc s k hfixed j

/--
[sixVertexCanonicalEvenChargeOffset_eq_boundary_add_commonDifference](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedOffset.lean)
-/
@[path]
private lemma sixVertexCanonicalEvenChargeOffset_eq_boundary_add_commonDifference_eq
  {c : Real}
  {s k : Nat}
  {j : Fin ((s + k + 1) + (s + k + 1))}
-- given
  (hc : 2 < c)
  (hfixed : SixVertexFixedEvenChargePerronBranchWitness c s k (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k)) :
-- imply
  sixVertexCanonicalEvenChargeOffset hc s k j = sixVertexCanonicalEvenOffsetBoundarySource hc s k j + ∑ l, (sixVertexTheta c (sixVertexCanonicalEvenAlignedHalfRoots hc s k j) (sixVertexCanonicalEvenAlignedHalfRoots hc s k l) - sixVertexTheta c (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k j) (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k l)) := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalEvenChargeOffset_eq_boundary_add_commonDifference hc s k hfixed j

/--
[abs_sixVertexCanonicalEvenOffsetNodalResidual_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedOffset.lean)
-/
@[path]
private lemma abs_sixVertexCanonicalEvenOffsetNodalResidual_le_eq
  {c : Real}
  {s k : Nat}
  {B : Real}
  {j : Fin ((s + k + 1) + (s + k + 1))}
-- given
  (hc : 2 < c)
  (hfixed : SixVertexFixedEvenChargePerronBranchWitness c s k (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k))
  (hB : 0 <= B)
  (hoffset : forall j, |sixVertexCanonicalEvenChargeOffset hc s k j| <= B) :
-- imply
  |sixVertexCanonicalEvenOffsetNodalResidual hc s k j| <= 4 * sixVertexThetaTaylorBound c * B ^ 2 / sixVertexFourWidth (2 * s) k := by
-- proof
  apply StatMech.FrontierD.abs_sixVertexCanonicalEvenOffsetNodalResidual_le hc s k hfixed hB hoffset j

/--
[sixVertexCanonicalOddHalfIndex_quantum_average](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedOffset.lean)
-/
@[path]
private lemma sixVertexCanonicalOddHalfIndex_quantum_average_eq
  {s k : Nat}
  {j : Fin (((s + k + 1) + 1) + (s + k + 1))} :
-- imply
  (sixVertexCentralQuantumNumber (sixVertexCanonicalOddLowerHalfIndex s k j) + sixVertexCentralQuantumNumber (sixVertexCanonicalOddUpperHalfIndex s k j)) / 2 = sixVertexCentralQuantumNumber j := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalOddHalfIndex_quantum_average s k j

/--
[sixVertexCanonicalOddChargeOffset_eq_thetaDifference](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedOffset.lean)
-/
@[path]
private lemma sixVertexCanonicalOddChargeOffset_eq_thetaDifference_eq
  {c : Real}
  {s k : Nat}
  {j : Fin (((s + k + 1) + 1) + (s + k + 1))}
-- given
  (hc : 2 < c)
  (hfixed : SixVertexFixedOddChargePerronBranchWitness c s k (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k)) :
-- imply
  sixVertexCanonicalOddChargeOffset hc s k j = ((∑ l, sixVertexTheta c (sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k) (sixVertexCanonicalOddLowerHalfIndex s k j)) (sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k) l)) + (∑ l, sixVertexTheta c (sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k) (sixVertexCanonicalOddUpperHalfIndex s k j)) (sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k) l))) / 2 - ∑ l, sixVertexTheta c (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k j) (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k l) := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalOddChargeOffset_eq_thetaDifference hc s k hfixed j

/--
[sixVertexCanonicalOddChargeOffset_eq_boundary_add_commonDifference](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedOffset.lean)
-/
@[path]
private lemma sixVertexCanonicalOddChargeOffset_eq_boundary_add_commonDifference_eq
  {c : Real}
  {s k : Nat}
  {j : Fin (((s + k + 1) + 1) + (s + k + 1))}
-- given
  (hc : 2 < c)
  (hfixed : SixVertexFixedOddChargePerronBranchWitness c s k (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k)) :
-- imply
  sixVertexCanonicalOddChargeOffset hc s k j = sixVertexCanonicalOddOffsetBoundarySource hc s k j + ∑ l, (sixVertexTheta c (sixVertexCanonicalOddAlignedHalfRoots hc s k j) (sixVertexCanonicalOddAlignedHalfRoots hc s k l) - sixVertexTheta c (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k j) (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k l)) := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalOddChargeOffset_eq_boundary_add_commonDifference hc s k hfixed j

/--
[abs_sixVertexCanonicalOddOffsetNodalResidual_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedOffset.lean)
-/
@[path]
private lemma abs_sixVertexCanonicalOddOffsetNodalResidual_le_eq
  {c : Real}
  {s k : Nat}
  {B : Real}
  {j : Fin (((s + k + 1) + 1) + (s + k + 1))}
-- given
  (hc : 2 < c)
  (hfixed : SixVertexFixedOddChargePerronBranchWitness c s k (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k))
  (hB : 0 <= B)
  (hoffset : forall j, |sixVertexCanonicalOddChargeOffset hc s k j| <= B) :
-- imply
  |sixVertexCanonicalOddOffsetNodalResidual hc s k j| <= 4 * sixVertexThetaTaylorBound c * B ^ 2 / sixVertexFourWidth (2 * s + 1) k := by
-- proof
  apply StatMech.FrontierD.abs_sixVertexCanonicalOddOffsetNodalResidual_le hc s k hfixed hB hoffset j


-- created on 2026-10-23
