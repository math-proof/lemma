import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheVandermonde.Part5
open Finset Filter Matrix Topology StatMech StatMech.FrontierD


/--
[tendsto_sixVertexNormalizedBethePairFactorAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheVandermonde.lean)
-/
@[path]
private lemma tendsto_sixVertexNormalizedBethePairFactorAt_eq
  {k : Nat}
  {i j : Fin ((k + 1) + (k + 1))} :
-- imply
  Tendsto (fun c => sixVertexNormalizedBethePairFactor c (sixVertexBethePhase (sixVertexHalfFilledBetheRootAt k i c)) (sixVertexBethePhase (sixVertexHalfFilledBetheRootAt k j c))) atTop (nhds (sixVertexHalfFilledLimitingPhase k i)) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexNormalizedBethePairFactorAt k i j

/--
[tendsto_sixVertexHalfFilledNormalizedAmplitude](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheVandermonde.lean)
-/
@[path]
private lemma tendsto_sixVertexHalfFilledNormalizedAmplitude_eq
  {k : Nat}
  {sigma : Equiv.Perm (Fin ((k + 1) + (k + 1)))} :
-- imply
  Tendsto (sixVertexHalfFilledNormalizedAmplitude k · sigma) atTop (nhds ((((Equiv.Perm.sign sigma : Int) : Complex)) * ∏ i, ∏ _j ∈ Finset.Ioi i, sixVertexHalfFilledLimitingPhase k (sigma i))) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexHalfFilledNormalizedAmplitude k sigma

/--
[tendsto_sixVertexHalfFilledNormalizedOddWave](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheVandermonde.lean)
-/
@[path]
private lemma tendsto_sixVertexHalfFilledNormalizedOddWave_eq
  {k : Nat} :
-- imply
  Tendsto (sixVertexHalfFilledNormalizedOddWave k) atTop (nhds (sixVertexHalfFilledVandermondeSum k)) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexHalfFilledNormalizedOddWave k

/--
[sixVertexHalfFilledVandermondeSum_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheVandermonde.lean)
-/
@[path]
private lemma sixVertexHalfFilledVandermondeSum_eq_eq
  {k : Nat} :
-- imply
  sixVertexHalfFilledVandermondeSum k = (∏ i, sixVertexHalfFilledLimitingPhase k i ^ ((k + 1) + (k + 1))) * (Matrix.vandermonde (sixVertexHalfFilledLimitingPhase k)).det := by
-- proof
  apply StatMech.FrontierD.sixVertexHalfFilledVandermondeSum_eq k

/--
[sixVertexHalfFilledVandermondeSum_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheVandermonde.lean)
-/
@[path]
private lemma sixVertexHalfFilledVandermondeSum_ne_zero_eq
  {k : Nat} :
-- imply
  sixVertexHalfFilledVandermondeSum k ≠ 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexHalfFilledVandermondeSum_ne_zero k

/--
[sixVertexHalfFilledPairScaleProduct_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheVandermonde.lean)
-/
@[path]
private lemma sixVertexHalfFilledPairScaleProduct_ne_zero_eq
  {c : Real}
  {k : Nat}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexHalfFilledPairScaleProduct k c ≠ 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexHalfFilledPairScaleProduct_ne_zero hc k

/--
[sixVertexCoordinateBetheWave_odd_eq_scale_mul_normalized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheVandermonde.lean)
-/
@[path]
private lemma sixVertexCoordinateBetheWave_odd_eq_scale_mul_normalized_eq
  {c : Real}
  {k : Nat}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexCoordinateBetheWave c (sixVertexHalfFilledBetheRoots hc k) (sixVertexAlternatingOddSector (sixVertexFourWidth 0 k) ((k + 1) + (k + 1)) (by unfold sixVertexFourWidth omega)) = sixVertexHalfFilledPairScaleProduct k c * sixVertexHalfFilledNormalizedOddWave k c := by
-- proof
  apply StatMech.FrontierD.sixVertexCoordinateBetheWave_odd_eq_scale_mul_normalized hc k

/--
[exists_sixVertexHalfFilledBetheRotatedRealWave_ne_zero_of_coordinate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheVandermonde.lean)
-/
@[path]
private lemma exists_sixVertexHalfFilledBetheRotatedRealWave_ne_zero_of_coordinate_eq
  {c : Real}
  {k : Nat}
  {x : SixVertexSector (sixVertexFourWidth 0 k) ((k + 1) + (k + 1))}
-- given
  (hc : 2 < c)
  (hx : sixVertexCoordinateBetheWave c (sixVertexHalfFilledBetheRoots hc k) x ≠ 0) :
-- imply
  ∃ a : Complex, sixVertexHalfFilledBetheRotatedRealWave hc k a ≠ 0 := by
-- proof
  apply StatMech.FrontierD.exists_sixVertexHalfFilledBetheRotatedRealWave_ne_zero_of_coordinate hc k x hx

/--
[eventually_exists_sixVertexHalfFilledBetheRotatedRealWave_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheVandermonde.lean)
-/
@[path]
private lemma eventually_exists_sixVertexHalfFilledBetheRotatedRealWave_ne_zero_eq
  {k : Nat} :
-- imply
  ∀ᶠ c : Real in atTop, ∀ hc : 2 < c, ∃ a : Complex, sixVertexHalfFilledBetheRotatedRealWave hc k a ≠ 0 := by
-- proof
  apply StatMech.FrontierD.eventually_exists_sixVertexHalfFilledBetheRotatedRealWave_ne_zero k

/--
[eventually_sixVertexHalfFilledBetheCandidateNormalized_eq_top_vandermonde](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheVandermonde.lean)
-/
@[path]
private lemma eventually_sixVertexHalfFilledBetheCandidateNormalized_eq_top_vandermonde_eq
  {k : Nat} :
-- imply
  ∀ᶠ c : Real in atTop, sixVertexHalfFilledBetheCandidateNormalized k c = sixVertexSectorTopEigenvalue (sixVertexFourWidth 0 k) ((k + 1) + (k + 1)) (by unfold sixVertexFourWidth omega) c / (c ^ 2 - 2) ^ ((k + 1) + (k + 1)) := by
-- proof
  apply StatMech.FrontierD.eventually_sixVertexHalfFilledBetheCandidateNormalized_eq_top_vandermonde k

/--
[eventually_sixVertexHalfFilledBetheCandidate_eq_top_vandermonde](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheVandermonde.lean)
-/
@[path]
private lemma eventually_sixVertexHalfFilledBetheCandidate_eq_top_vandermonde_eq
  {k : Nat} :
-- imply
  ∀ᶠ c : Real in atTop, ∀ hc : 2 < c, sixVertexSymmetricBetheEigenvalueValue c (sixVertexPositiveHalfBetheRoots hc k) = sixVertexSectorTopEigenvalue (sixVertexFourWidth 0 k) ((k + 1) + (k + 1)) (by unfold sixVertexFourWidth omega) c := by
-- proof
  apply StatMech.FrontierD.eventually_sixVertexHalfFilledBetheCandidate_eq_top_vandermonde k


-- created on 2026-10-23
