import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetFinite.Part2
open Finset StatMech StatMech.FrontierD


/--
[sixVertexEvenChargeHalfIndex_quantum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetFinite.lean)
-/
@[path]
private lemma sixVertexEvenChargeHalfIndex_quantum_eq
  {s k : Nat}
  {j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s) k)} :
-- imply
  sixVertexCentralQuantumNumber (sixVertexEvenChargeHalfIndex s k j) = sixVertexCentralQuantumNumber j := by
-- proof
  apply StatMech.FrontierD.sixVertexEvenChargeHalfIndex_quantum s k j

/--
[sixVertexOddChargeHalfIndex_quantum_average](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetFinite.lean)
-/
@[path]
private lemma sixVertexOddChargeHalfIndex_quantum_average_eq
  {s k : Nat}
  {j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k)} :
-- imply
  (sixVertexCentralQuantumNumber (sixVertexOddChargeLowerHalfIndex s k j) + sixVertexCentralQuantumNumber (sixVertexOddChargeUpperHalfIndex s k j)) / 2 = sixVertexCentralQuantumNumber j := by
-- proof
  apply StatMech.FrontierD.sixVertexOddChargeHalfIndex_quantum_average s k j

/--
[sixVertexEvenChargeBetheOffset_eq_thetaDifference](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetFinite.lean)
-/
@[path]
private lemma sixVertexEvenChargeBetheOffset_eq_thetaDifference_eq
  {c : Real}
  {s k : Nat}
  {j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s) k)}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexEvenChargeBetheOffset hc s k j = (∑ l, sixVertexTheta c (sixVertexHalfFilledBetheRoots hc (2 * s + k) (sixVertexEvenChargeHalfIndex s k j)) (sixVertexHalfFilledBetheRoots hc (2 * s + k) l)) - ∑ l, sixVertexTheta c (sixVertexFixedChargeBetheRoots hc (2 * s) k j) (sixVertexFixedChargeBetheRoots hc (2 * s) k l) := by
-- proof
  apply StatMech.FrontierD.sixVertexEvenChargeBetheOffset_eq_thetaDifference hc s k j

/--
[sixVertexOddChargeBetheOffset_eq_thetaDifference](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetFinite.lean)
-/
@[path]
private lemma sixVertexOddChargeBetheOffset_eq_thetaDifference_eq
  {c : Real}
  {s k : Nat}
  {j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k)}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexOddChargeBetheOffset hc s k j = ((∑ l, sixVertexTheta c (sixVertexHalfFilledBetheRoots hc (2 * s + 1 + k) (sixVertexOddChargeLowerHalfIndex s k j)) (sixVertexHalfFilledBetheRoots hc (2 * s + 1 + k) l)) + (∑ l, sixVertexTheta c (sixVertexHalfFilledBetheRoots hc (2 * s + 1 + k) (sixVertexOddChargeUpperHalfIndex s k j)) (sixVertexHalfFilledBetheRoots hc (2 * s + 1 + k) l))) / 2 - ∑ l, sixVertexTheta c (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k j) (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k l) := by
-- proof
  apply StatMech.FrontierD.sixVertexOddChargeBetheOffset_eq_thetaDifference hc s k j

/--
[sixVertexOddChargeBetheOffset_central_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetFinite.lean)
-/
@[path]
private lemma sixVertexOddChargeBetheOffset_central_eq_zero_eq
  {c : Real}
  {s k : Nat}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexOddChargeBetheOffset hc s k (sixVertexFixedChargeBetheCentralIndex (2 * s + 1) k) = 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexOddChargeBetheOffset_central_eq_zero hc s k


-- created on 2026-10-23
