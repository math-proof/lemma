import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetSymmetry
open StatMech StatMech.FrontierD


/--
[sum_fin_eq_zero_of_rev_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetSymmetry.lean)
-/
@[path]
private lemma sum_fin_eq_zero_of_rev_neg_eq
  {n : Nat}
  {f : Fin n → Real}
-- given
  (hf : ∀ j, f j.rev = -f j) :
-- imply
  ∑ j, f j = 0 := by
-- proof
  apply StatMech.FrontierD.sum_fin_eq_zero_of_rev_neg hf

/--
[sixVertexFiniteRootDensity_neg_of_symmetric](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetSymmetry.lean)
-/
@[path]
private lemma sixVertexFiniteRootDensity_neg_of_symmetric_eq
  {c : Real}
  {N n : Nat}
  {p : Fin n → Real}
  {x : Real}
-- given
  (hp : SixVertexRootSymmetric p) :
-- imply
  sixVertexFiniteRootDensity c N n p (-x) = sixVertexFiniteRootDensity c N n p x := by
-- proof
  apply StatMech.FrontierD.sixVertexFiniteRootDensity_neg_of_symmetric hp x

/--
[sixVertexEvenChargeHalfIndex_rev](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetSymmetry.lean)
-/
@[path]
private lemma sixVertexEvenChargeHalfIndex_rev_eq
  {s k : Nat}
  {j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s) k)} :
-- imply
  (sixVertexEvenChargeHalfIndex s k j).rev = sixVertexEvenChargeHalfIndex s k j.rev := by
-- proof
  apply StatMech.FrontierD.sixVertexEvenChargeHalfIndex_rev s k j

/--
[sixVertexOddChargeLowerHalfIndex_rev](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetSymmetry.lean)
-/
@[path]
private lemma sixVertexOddChargeLowerHalfIndex_rev_eq
  {s k : Nat}
  {j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k)} :
-- imply
  sixVertexOddChargeLowerHalfIndex s k j.rev = (sixVertexOddChargeUpperHalfIndex s k j).rev := by
-- proof
  apply StatMech.FrontierD.sixVertexOddChargeLowerHalfIndex_rev s k j

/--
[sixVertexOddChargeUpperHalfIndex_rev](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetSymmetry.lean)
-/
@[path]
private lemma sixVertexOddChargeUpperHalfIndex_rev_eq
  {s k : Nat}
  {j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k)} :
-- imply
  sixVertexOddChargeUpperHalfIndex s k j.rev = (sixVertexOddChargeLowerHalfIndex s k j).rev := by
-- proof
  apply StatMech.FrontierD.sixVertexOddChargeUpperHalfIndex_rev s k j

/--
[sixVertexEvenChargeBetheOffset_rev](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetSymmetry.lean)
-/
@[path]
private lemma sixVertexEvenChargeBetheOffset_rev_eq
  {c : Real}
  {s k : Nat}
  {j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s) k)}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexEvenChargeBetheOffset hc s k j.rev = -sixVertexEvenChargeBetheOffset hc s k j := by
-- proof
  apply StatMech.FrontierD.sixVertexEvenChargeBetheOffset_rev hc s k j

/--
[sixVertexOddChargeBetheOffset_rev](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetSymmetry.lean)
-/
@[path]
private lemma sixVertexOddChargeBetheOffset_rev_eq
  {c : Real}
  {s k : Nat}
  {j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k)}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexOddChargeBetheOffset hc s k j.rev = -sixVertexOddChargeBetheOffset hc s k j := by
-- proof
  apply StatMech.FrontierD.sixVertexOddChargeBetheOffset_rev hc s k j

/--
[sum_evenChargeWeightedOffsetError_div_weight_density_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetSymmetry.lean)
-/
@[path]
private lemma sum_evenChargeWeightedOffsetError_div_weight_density_eq_zero_eq
  {c : Real}
  {s k : Nat}
  {tau : Real → Real}
  {a : Real}
-- given
  (hc : 2 < c)
  (htau : Function.Odd tau) :
-- imply
  ∑ j, (sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s) k) (sixVertexFixedChargeBetheParticleCount (2 * s) k) (sixVertexFixedChargeBetheRoots hc (2 * s) k) (sixVertexFixedChargeBetheRoots hc (2 * s) k j) * sixVertexEvenChargeBetheOffset hc s k j - a * tau (sixVertexFixedChargeBetheRoots hc (2 * s) k j)) / (sixVertexRootDensityWeight c (sixVertexFixedChargeBetheRoots hc (2 * s) k j) * sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s) k) (sixVertexFixedChargeBetheParticleCount (2 * s) k) (sixVertexFixedChargeBetheRoots hc (2 * s) k) (sixVertexFixedChargeBetheRoots hc (2 * s) k j)) = 0 := by
-- proof
  apply StatMech.FrontierD.sum_evenChargeWeightedOffsetError_div_weight_density_eq_zero hc s k htau a

/--
[sum_oddChargeWeightedOffsetError_div_weight_density_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetSymmetry.lean)
-/
@[path]
private lemma sum_oddChargeWeightedOffsetError_div_weight_density_eq_zero_eq
  {c : Real}
  {s k : Nat}
  {tau : Real → Real}
  {a : Real}
-- given
  (hc : 2 < c)
  (htau : Function.Odd tau) :
-- imply
  ∑ j, (sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k) (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k) (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k) (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k j) * sixVertexOddChargeBetheOffset hc s k j - a * tau (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k j)) / (sixVertexRootDensityWeight c (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k j) * sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k) (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k) (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k) (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k j)) = 0 := by
-- proof
  apply StatMech.FrontierD.sum_oddChargeWeightedOffsetError_div_weight_density_eq_zero hc s k htau a


-- created on 2026-10-23
