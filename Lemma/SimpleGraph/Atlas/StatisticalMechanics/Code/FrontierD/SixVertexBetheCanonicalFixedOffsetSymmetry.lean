import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedOffsetSymmetry
open StatMech StatMech.FrontierD


/--
[sixVertexCanonicalEvenHalfIndex_rev](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedOffsetSymmetry.lean)
-/
@[path]
private lemma sixVertexCanonicalEvenHalfIndex_rev_eq
  {s k : Nat}
  {j : Fin ((s + k + 1) + (s + k + 1))} :
-- imply
  sixVertexCanonicalEvenHalfIndex s k j.rev = (sixVertexCanonicalEvenHalfIndex s k j).rev := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalEvenHalfIndex_rev s k j

/--
[sixVertexCanonicalEvenAlignedHalfRoots_rev](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedOffsetSymmetry.lean)
-/
@[path]
private lemma sixVertexCanonicalEvenAlignedHalfRoots_rev_eq
  {c : Real}
  {s k : Nat}
  {j : Fin ((s + k + 1) + (s + k + 1))}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexCanonicalEvenAlignedHalfRoots hc s k j.rev = -sixVertexCanonicalEvenAlignedHalfRoots hc s k j := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalEvenAlignedHalfRoots_rev hc s k j

/--
[sixVertexCanonicalEvenChargeOffset_rev](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedOffsetSymmetry.lean)
-/
@[path]
private lemma sixVertexCanonicalEvenChargeOffset_rev_eq
  {c : Real}
  {s k : Nat}
  {j : Fin ((s + k + 1) + (s + k + 1))}
-- given
  (hc : 2 < c)
  (hfixed : SixVertexFixedEvenChargePerronBranchWitness c s k (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k)) :
-- imply
  sixVertexCanonicalEvenChargeOffset hc s k j.rev = -sixVertexCanonicalEvenChargeOffset hc s k j := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalEvenChargeOffset_rev hc s k hfixed j

/--
[sixVertexCanonicalOddLowerHalfIndex_rev](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedOffsetSymmetry.lean)
-/
@[path]
private lemma sixVertexCanonicalOddLowerHalfIndex_rev_eq
  {s k : Nat}
  {j : Fin (((s + k + 1) + 1) + (s + k + 1))} :
-- imply
  sixVertexCanonicalOddLowerHalfIndex s k j.rev = (sixVertexCanonicalOddUpperHalfIndex s k j).rev := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalOddLowerHalfIndex_rev s k j

/--
[sixVertexCanonicalOddUpperHalfIndex_rev](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedOffsetSymmetry.lean)
-/
@[path]
private lemma sixVertexCanonicalOddUpperHalfIndex_rev_eq
  {s k : Nat}
  {j : Fin (((s + k + 1) + 1) + (s + k + 1))} :
-- imply
  sixVertexCanonicalOddUpperHalfIndex s k j.rev = (sixVertexCanonicalOddLowerHalfIndex s k j).rev := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalOddUpperHalfIndex_rev s k j

/--
[sixVertexCanonicalOddAlignedHalfRoots_rev](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedOffsetSymmetry.lean)
-/
@[path]
private lemma sixVertexCanonicalOddAlignedHalfRoots_rev_eq
  {c : Real}
  {s k : Nat}
  {j : Fin (((s + k + 1) + 1) + (s + k + 1))}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexCanonicalOddAlignedHalfRoots hc s k j.rev = -sixVertexCanonicalOddAlignedHalfRoots hc s k j := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalOddAlignedHalfRoots_rev hc s k j

/--
[sixVertexCanonicalOddChargeOffset_rev](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedOffsetSymmetry.lean)
-/
@[path]
private lemma sixVertexCanonicalOddChargeOffset_rev_eq
  {c : Real}
  {s k : Nat}
  {j : Fin (((s + k + 1) + 1) + (s + k + 1))}
-- given
  (hc : 2 < c)
  (hfixed : SixVertexFixedOddChargePerronBranchWitness c s k (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k)) :
-- imply
  sixVertexCanonicalOddChargeOffset hc s k j.rev = -sixVertexCanonicalOddChargeOffset hc s k j := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalOddChargeOffset_rev hc s k hfixed j

/--
[sum_weightedOffsetError_div_weight_density_eq_zero_of_rev](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedOffsetSymmetry.lean)
-/
@[path]
private lemma sum_weightedOffsetError_div_weight_density_eq_zero_of_rev_eq
  {c : Real}
  {N n : Nat}
  {p eps : Fin n -> Real}
  {tau : Real -> Real}
  {a : Real}
-- given
  (hp : forall j, p j.rev = -p j)
  (heps : forall j, eps j.rev = -eps j)
  (htau : Function.Odd tau) :
-- imply
  ∑ j, (sixVertexFiniteRootDensity c N n p (p j) * eps j - a * tau (p j)) / (sixVertexRootDensityWeight c (p j) * sixVertexFiniteRootDensity c N n p (p j)) = 0 := by
-- proof
  apply StatMech.FrontierD.sum_weightedOffsetError_div_weight_density_eq_zero_of_rev hp heps htau a

/--
[sum_sixVertexCanonicalEvenWeightedOffsetError_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedOffsetSymmetry.lean)
-/
@[path]
private lemma sum_sixVertexCanonicalEvenWeightedOffsetError_eq_zero_eq
  {c : Real}
  {s k : Nat}
  {tau : Real -> Real}
  {a : Real}
-- given
  (hc : 2 < c)
  (hfixed : SixVertexFixedEvenChargePerronBranchWitness c s k (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k))
  (htau : Function.Odd tau) :
-- imply
  ∑ j, (sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s) k) ((s + k + 1) + (s + k + 1)) (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k) (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k j) * sixVertexCanonicalEvenChargeOffset hc s k j - a * tau (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k j)) / (sixVertexRootDensityWeight c (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k j) * sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s) k) ((s + k + 1) + (s + k + 1)) (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k) (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k j)) = 0 := by
-- proof
  apply StatMech.FrontierD.sum_sixVertexCanonicalEvenWeightedOffsetError_eq_zero hc s k hfixed htau a

/--
[sum_sixVertexCanonicalOddWeightedOffsetError_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedOffsetSymmetry.lean)
-/
@[path]
private lemma sum_sixVertexCanonicalOddWeightedOffsetError_eq_zero_eq
  {c : Real}
  {s k : Nat}
  {tau : Real -> Real}
  {a : Real}
-- given
  (hc : 2 < c)
  (hfixed : SixVertexFixedOddChargePerronBranchWitness c s k (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k))
  (htau : Function.Odd tau) :
-- imply
  ∑ j, (sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k) (((s + k + 1) + 1) + (s + k + 1)) (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k) (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k j) * sixVertexCanonicalOddChargeOffset hc s k j - a * tau (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k j)) / (sixVertexRootDensityWeight c (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k j) * sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k) (((s + k + 1) + 1) + (s + k + 1)) (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k) (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k j)) = 0 := by
-- proof
  apply StatMech.FrontierD.sum_sixVertexCanonicalOddWeightedOffsetError_eq_zero hc s k hfixed htau a


-- created on 2026-10-23
