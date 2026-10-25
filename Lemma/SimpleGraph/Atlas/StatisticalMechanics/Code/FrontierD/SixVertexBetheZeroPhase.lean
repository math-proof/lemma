import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheZeroPhase.Part7
open Finset StatMech StatMech.FrontierD


/--
[continuous_sixVertexCoordinateBetheWave_roots](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhase.lean)
-/
@[path]
private lemma continuous_sixVertexCoordinateBetheWave_roots_eq
  {N n : Nat}
  {c : Real}
  {x : SixVertexSector N n} :
-- imply
  Continuous (fun p : Fin n -> Real => sixVertexCoordinateBetheWave c p x) := by
-- proof
  apply StatMech.FrontierD.continuous_sixVertexCoordinateBetheWave_roots c x

/--
[sixVertexBethe_intervalLocalSum_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhase.lean)
-/
@[path]
private lemma sixVertexBethe_intervalLocalSum_one_eq
  {c : Real}
  {a b : Int}
-- given
  (hab : a < b) :
-- imply
  (∑ y ∈ Finset.Icc a b, (if y = a ∨ y = b then 1 else (c : Complex) ^ 2) * (1 : Complex) ^ y) = 2 + ((b - a - 1).toNat : Complex) * (c : Complex) ^ 2 := by
-- proof
  apply StatMech.FrontierD.sixVertexBethe_intervalLocalSum_one c hab

/--
[sixVertexBetheIntervalTupleWeight_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhase.lean)
-/
@[path]
private lemma sixVertexBetheIntervalTupleWeight_factor_eq
  {n : Nat}
  {N : Nat}
  {c : Real}
-- given
  (z : Fin (n + 1) -> Complex)
  (x q : Fin (n + 1) -> Int) :
-- imply
  sixVertexBetheIntervalTupleWeight N c z x q = ((c : Complex) ^ 2) ^ (sixVertexBetheInteriorSet N x q).card * ∏ i, z i ^ q i := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheIntervalTupleWeight_factor N c z x q

/--
[sixVertexBetheCollisionConstrainedIntervalSum_zeroPhase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhase.lean)
-/
@[path]
private lemma sixVertexBetheCollisionConstrainedIntervalSum_zeroPhase_eq
  {n : Nat}
  {N : Nat}
  {c : Real}
  {S : Finset (Fin (n + 1))}
  {ell : Fin (n + 1)}
-- given
  (p : Fin (n + 1) -> Real)
  (x : Fin (n + 1) -> Int)
  (hell : p ell = 0)
  (hS : SixVertexBetheNoAdjacent S)
  (hgap : ∀ i, sixVertexBetheShiftCoordinates N x i < x i) :
-- imply
  sixVertexBetheCollisionConstrainedIntervalSum N c (fun i => sixVertexBethePhase (p i)) x S = (if ell ∈ S then 1 else if (finRotate (n + 1)).symm ell ∈ S then 1 else 2 + ((x ell - sixVertexBetheShiftCoordinates N x ell - 1).toNat : Complex) * (c : Complex) ^ 2) * ∏ i ∈ (Finset.univ.erase ell), ∑ y ∈ sixVertexBetheConstrainedCoordinateSet N x S i, (if y = sixVertexBetheShiftCoordinates N x i ∨ y = x i then 1 else (c : Complex) ^ 2) * sixVertexBethePhase (p i) ^ y := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheCollisionConstrainedIntervalSum_zeroPhase N c p x S ell hell hS hgap

/--
[sixVertexBetheCollisionConstrainedIntervalSum_zero_of_adjacent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhase.lean)
-/
@[path]
private lemma sixVertexBetheCollisionConstrainedIntervalSum_zero_of_adjacent_eq
  {n : Nat}
  {N : Nat}
  {c : Real}
  {S : Finset (Fin (n + 1))}
-- given
  (z : Fin (n + 1) -> Complex)
  (x : Fin (n + 1) -> Int)
  (hgap : ∀ i, sixVertexBetheShiftCoordinates N x i < x i)
  (hS : ¬ SixVertexBetheNoAdjacent S) :
-- imply
  sixVertexBetheCollisionConstrainedIntervalSum N c z x S = 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheCollisionConstrainedIntervalSum_zero_of_adjacent N c z x S hgap hS

/--
[sixVertexBetheCollisionFreeIntervalSum_zeroPhase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhase.lean)
-/
@[path]
private lemma sixVertexBetheCollisionFreeIntervalSum_zeroPhase_eq
  {n : Nat}
  {N : Nat}
  {c : Real}
  {ell : Fin (n + 1)}
-- given
  (p : Fin (n + 1) -> Real)
  (x : Fin (n + 1) -> Int)
  (hell : p ell = 0)
  (hgap : ∀ i, sixVertexBetheShiftCoordinates N x i < x i) :
-- imply
  sixVertexBetheCollisionFreeIntervalSum N c (fun i => sixVertexBethePhase (p i)) x = sixVertexBetheZeroPhaseRegularizedIntervalSum N c p x ell := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheCollisionFreeIntervalSum_zeroPhase N c p x ell hell hgap

/--
[SixVertexSatisfiesMultiplicativeBetheEquations.physicalZeroPhaseIntervalExpansion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhase.lean)
-/
@[path]
private lemma physicalZeroPhaseIntervalExpansion_eq
  {c : Real}
  {N n : Nat}
  {ell : Fin (n + 1)}
  {x : SixVertexSector N (n + 1)}
-- given
  (hc : 2 < c)
  (p : Fin (n + 1) -> Real)
  (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 1) p)
  (hell : p ell = 0) :
-- imply
  (sixVertexSectorTransferComplex N (n + 1) c).mulVec (sixVertexCoordinateBetheWave c p) x = ∑ sigma : Equiv.Perm (Fin (n + 1)), sixVertexBetheAmplitude c p sigma * sixVertexBetheZeroPhaseRegularizedIntervalSum N c (fun i => p (sigma i)) (sixVertexSectorIntCoordinates x) (sigma.symm ell) := by
-- proof
  apply StatMech.FrontierD.SixVertexSatisfiesMultiplicativeBetheEquations.physicalZeroPhaseIntervalExpansion hc p hp ell hell x

/--
[hasDerivAt_sixVertexTheta_zero_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhase.lean)
-/
@[path]
private lemma hasDerivAt_sixVertexTheta_zero_left_eq
  {c : Real}
  {y : Real}
-- given
  (hc : 2 < c) :
-- imply
  HasDerivAt (fun x => sixVertexTheta c x y) (sixVertexThetaLeftDerivAtZero c y) 0 := by
-- proof
  apply StatMech.FrontierD.hasDerivAt_sixVertexTheta_zero_left hc y

/--
[sixVertexThetaLeftDerivAtZero_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhase.lean)
-/
@[path]
private lemma sixVertexThetaLeftDerivAtZero_self_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexThetaLeftDerivAtZero c 0 = 2 / c ^ 2 - 1 := by
-- proof
  apply StatMech.FrontierD.sixVertexThetaLeftDerivAtZero_self hc

/--
[neg_two_lt_sixVertexThetaLeftDerivAtZero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhase.lean)
-/
@[path]
private lemma neg_two_lt_sixVertexThetaLeftDerivAtZero_eq
  {c : Real}
  {y : Real}
-- given
  (hc : 2 < c) :
-- imply
  -2 < sixVertexThetaLeftDerivAtZero c y := by
-- proof
  apply StatMech.FrontierD.neg_two_lt_sixVertexThetaLeftDerivAtZero hc y

/--
[sixVertexZeroPhaseBethePrefactor_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhase.lean)
-/
@[path]
private lemma sixVertexZeroPhaseBethePrefactor_eq_eq
  {n : Nat}
  {c : Real}
  {N : Nat}
  {ell : Fin n}
-- given
  (hc : 2 < c)
  (p : Fin n -> Real)
  (hell : p ell = 0) :
-- imply
  sixVertexZeroPhaseBethePrefactor c N p ell = c ^ 2 * ((N : Real) + ∑ j, sixVertexThetaLeftDerivAtZero c (p j)) := by
-- proof
  apply StatMech.FrontierD.sixVertexZeroPhaseBethePrefactor_eq hc N p ell hell

/--
[sixVertexZeroPhaseBethePrefactor_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhase.lean)
-/
@[path]
private lemma sixVertexZeroPhaseBethePrefactor_pos_eq
  {n N : Nat}
  {c : Real}
  {ell : Fin n}
-- given
  (hc : 2 < c)
  (hhalf : 2 * n <= N)
  (p : Fin n -> Real)
  (hell : p ell = 0) :
-- imply
  0 < sixVertexZeroPhaseBethePrefactor c N p ell := by
-- proof
  apply StatMech.FrontierD.sixVertexZeroPhaseBethePrefactor_pos hc hhalf p ell hell

/--
[sixVertexThetaLeftDerivAtZero_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhase.lean)
-/
@[path]
private lemma sixVertexThetaLeftDerivAtZero_neg_eq
  {c : Real}
  {y : Real}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexThetaLeftDerivAtZero c y < 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexThetaLeftDerivAtZero_neg hc y

/--
[sixVertexZeroPhaseBethePrefactor_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhase.lean)
-/
@[path]
private lemma sixVertexZeroPhaseBethePrefactor_bounds_eq
  {n N : Nat}
  {c : Real}
  {ell : Fin n}
-- given
  (hc : 2 < c)
  (p : Fin n -> Real)
  (hell : p ell = 0) :
-- imply
  c ^ 2 * ((N : Real) - 2 * (n : Real)) < sixVertexZeroPhaseBethePrefactor c N p ell ∧ sixVertexZeroPhaseBethePrefactor c N p ell <= c ^ 2 * (N : Real) := by
-- proof
  apply StatMech.FrontierD.sixVertexZeroPhaseBethePrefactor_bounds hc p ell hell

/--
[sixVertexCoordinateBetheZeroPhaseEigenrelation_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhase.lean)
-/
@[path]
private lemma sixVertexCoordinateBetheZeroPhaseEigenrelation_one_eq
  {N : Nat}
  {c : Real}
-- given
  (p : Fin 1 -> Real)
  (hp : p 0 = 0) :
-- imply
  SixVertexCoordinateBetheZeroPhaseEigenrelation (N := N) c p 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexCoordinateBetheZeroPhaseEigenrelation_one c p hp

/--
[norm_sixVertexZeroPhaseBetheEigenvalueCandidate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhase.lean)
-/
@[path]
private lemma norm_sixVertexZeroPhaseBetheEigenvalueCandidate_eq
  {n N : Nat}
  {c : Real}
  {ell : Fin n}
-- given
  (hc : 2 < c)
  (hhalf : 2 * n <= N)
  (p : Fin n -> Real)
  (hell : p ell = 0) :
-- imply
  ‖sixVertexZeroPhaseBetheEigenvalueCandidate c N p ell‖ = sixVertexZeroPhaseBetheEigenvalueValue c N p ell := by
-- proof
  apply StatMech.FrontierD.norm_sixVertexZeroPhaseBetheEigenvalueCandidate hc hhalf p ell hell

/--
[sixVertexZeroPhaseBetheEigenvalueValue_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhase.lean)
-/
@[path]
private lemma sixVertexZeroPhaseBetheEigenvalueValue_pos_eq
  {n N : Nat}
  {c : Real}
  {ell : Fin n}
-- given
  (hc : 2 < c)
  (hhalf : 2 * n <= N)
  (p : Fin n -> Real)
  (hell : p ell = 0) :
-- imply
  0 < sixVertexZeroPhaseBetheEigenvalueValue c N p ell := by
-- proof
  apply StatMech.FrontierD.sixVertexZeroPhaseBetheEigenvalueValue_pos hc hhalf p ell hell

/--
[sixVertexZeroPhaseBetheEigenvalueValue_log](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhase.lean)
-/
@[path]
private lemma sixVertexZeroPhaseBetheEigenvalueValue_log_eq
  {n N : Nat}
  {c : Real}
  {ell : Fin n}
-- given
  (hc : 2 < c)
  (hhalf : 2 * n <= N)
  (p : Fin n -> Real)
  (hell : p ell = 0) :
-- imply
  Real.log (sixVertexZeroPhaseBetheEigenvalueValue c N p ell) = Real.log (sixVertexZeroPhaseBethePrefactor c N p ell) + ∑ j ∈ (Finset.univ.erase ell), Real.log ‖sixVertexBetheM c (sixVertexBethePhase (p j))‖ := by
-- proof
  apply StatMech.FrontierD.sixVertexZeroPhaseBetheEigenvalueValue_log hc hhalf p ell hell

/--
[norm_sixVertexFixedOddChargeBetheEigenvalueCandidate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhase.lean)
-/
@[path]
private lemma norm_sixVertexFixedOddChargeBetheEigenvalueCandidate_eq
  {c : Real}
  {r : Nat}
  {k : Nat}
-- given
  (hc : 2 < c)
  (hr : Odd r) :
-- imply
  ‖sixVertexFixedOddChargeBetheEigenvalueCandidate hc r k‖ = sixVertexFixedOddChargeBetheEigenvalueValue hc r k := by
-- proof
  apply StatMech.FrontierD.norm_sixVertexFixedOddChargeBetheEigenvalueCandidate hc hr k

/--
[sixVertexFixedOddChargeBethePrefactor_div_width_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhase.lean)
-/
@[path]
private lemma sixVertexFixedOddChargeBethePrefactor_div_width_eq_eq
  {c : Real}
  {r : Nat}
  {k : Nat}
-- given
  (hc : 2 < c)
  (hr : Odd r) :
-- imply
  sixVertexZeroPhaseBethePrefactor c (sixVertexFourWidth r k) (sixVertexFixedChargeBetheRoots hc r k) (sixVertexFixedChargeBetheCentralIndex r k) / (sixVertexFourWidth r k : Real) = c ^ 2 * (1 + (∑ j, sixVertexThetaLeftDerivAtZero c (sixVertexFixedChargeBetheRoots hc r k j)) / (sixVertexFourWidth r k : Real)) := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedOddChargeBethePrefactor_div_width_eq hc hr k

/--
[sixVertexFixedOddChargeBethePrefactor_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhase.lean)
-/
@[path]
private lemma sixVertexFixedOddChargeBethePrefactor_bounds_eq
  {c : Real}
  {r : Nat}
  {k : Nat}
-- given
  (hc : 2 < c)
  (hr : Odd r) :
-- imply
  c ^ 2 * (2 * (r : Real)) < sixVertexZeroPhaseBethePrefactor c (sixVertexFourWidth r k) (sixVertexFixedChargeBetheRoots hc r k) (sixVertexFixedChargeBetheCentralIndex r k) ∧ sixVertexZeroPhaseBethePrefactor c (sixVertexFourWidth r k) (sixVertexFixedChargeBetheRoots hc r k) (sixVertexFixedChargeBetheCentralIndex r k) <= c ^ 2 * (sixVertexFourWidth r k : Real) := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedOddChargeBethePrefactor_bounds hc hr k

/--
[sixVertexFixedOddChargeEmpiricalThetaDerivative_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhase.lean)
-/
@[path]
private lemma sixVertexFixedOddChargeEmpiricalThetaDerivative_bounds_eq
  {c : Real}
  {r : Nat}
  {k : Nat}
-- given
  (hc : 2 < c)
  (hr : Odd r) :
-- imply
  -(1 : Real) + 2 * (r : Real) / (sixVertexFourWidth r k : Real) < (∑ j, sixVertexThetaLeftDerivAtZero c (sixVertexFixedChargeBetheRoots hc r k j)) / (sixVertexFourWidth r k : Real) ∧ (∑ j, sixVertexThetaLeftDerivAtZero c (sixVertexFixedChargeBetheRoots hc r k j)) / (sixVertexFourWidth r k : Real) <= 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedOddChargeEmpiricalThetaDerivative_bounds hc hr k

/--
[sixVertexFixedOddChargeBetheEigenvalueValue_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhase.lean)
-/
@[path]
private lemma sixVertexFixedOddChargeBetheEigenvalueValue_pos_eq
  {c : Real}
  {r : Nat}
  {k : Nat}
-- given
  (hc : 2 < c)
  (hr : Odd r) :
-- imply
  0 < sixVertexFixedOddChargeBetheEigenvalueValue hc r k := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedOddChargeBetheEigenvalueValue_pos hc hr k

/--
[sixVertexFixedOddChargeBetheEigenvalueValue_log](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhase.lean)
-/
@[path]
private lemma sixVertexFixedOddChargeBetheEigenvalueValue_log_eq
  {c : Real}
  {r : Nat}
  {k : Nat}
-- given
  (hc : 2 < c)
  (hr : Odd r) :
-- imply
  Real.log (sixVertexFixedOddChargeBetheEigenvalueValue hc r k) = Real.log (sixVertexZeroPhaseBethePrefactor c (sixVertexFourWidth r k) (sixVertexFixedChargeBetheRoots hc r k) (sixVertexFixedChargeBetheCentralIndex r k)) + ∑ j ∈ (Finset.univ.erase (sixVertexFixedChargeBetheCentralIndex r k)), Real.log ‖sixVertexBetheM c (sixVertexBethePhase (sixVertexFixedChargeBetheRoots hc r k j))‖ := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedOddChargeBetheEigenvalueValue_log hc hr k


-- created on 2026-10-23
