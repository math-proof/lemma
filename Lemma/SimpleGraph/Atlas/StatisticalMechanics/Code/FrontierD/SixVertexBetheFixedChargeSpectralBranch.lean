import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeSpectralBranch
open Finset Filter Matrix Topology StatMech StatMech.FrontierD


/--
[sixVertexFixedChargeBetheRotatedRealWave_eigenrelation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeSpectralBranch.lean)
-/
@[path]
private lemma sixVertexFixedChargeBetheRotatedRealWave_eigenrelation_eq
  {c μ : Real}
  {r k : Nat}
  {a : Complex}
-- given
  (hc : 2 < c)
  (hrelation : (sixVertexSectorTransferComplex (sixVertexFourWidth r k) (sixVertexFixedChargeBetheParticleCount r k) c).mulVec (sixVertexCoordinateBetheWave c (sixVertexFixedChargeBetheRoots hc r k)) = (μ : Complex) • sixVertexCoordinateBetheWave c (sixVertexFixedChargeBetheRoots hc r k)) :
-- imply
  sixVertexSectorTransfer (sixVertexFourWidth r k) (sixVertexFixedChargeBetheParticleCount r k) c *ᵥ sixVertexFixedChargeBetheRotatedRealWave hc r k a = μ • sixVertexFixedChargeBetheRotatedRealWave hc r k a := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedChargeBetheRotatedRealWave_eigenrelation hc r k hrelation a

/--
[exists_sixVertexFixedChargeBetheRotatedRealWave_ne_zero_of_coordinate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeSpectralBranch.lean)
-/
@[path]
private lemma exists_sixVertexFixedChargeBetheRotatedRealWave_ne_zero_of_coordinate_eq
  {c : Real}
  {r k : Nat}
  {x : SixVertexSector (sixVertexFourWidth r k) (sixVertexFixedChargeBetheParticleCount r k)}
-- given
  (hc : 2 < c)
  (hx : sixVertexCoordinateBetheWave c (sixVertexFixedChargeBetheRoots hc r k) x ≠ 0) :
-- imply
  ∃ a : Complex, sixVertexFixedChargeBetheRotatedRealWave hc r k a ≠ 0 := by
-- proof
  apply StatMech.FrontierD.exists_sixVertexFixedChargeBetheRotatedRealWave_ne_zero_of_coordinate hc r k x hx

/--
[eventually_exists_sixVertexFixedChargeBetheRotatedRealWave_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeSpectralBranch.lean)
-/
@[path]
private lemma eventually_exists_sixVertexFixedChargeBetheRotatedRealWave_ne_zero_eq
  {r k : Nat} :
-- imply
  ∀ᶠ c : Real in atTop, ∀ hc : 2 < c, ∃ a : Complex, sixVertexFixedChargeBetheRotatedRealWave hc r k a ≠ 0 := by
-- proof
  apply StatMech.FrontierD.eventually_exists_sixVertexFixedChargeBetheRotatedRealWave_ne_zero r k

/--
[eventually_sixVertexFixedEvenChargeBetheCandidateNormalized_hasEigenvalue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeSpectralBranch.lean)
-/
@[path]
private lemma eventually_sixVertexFixedEvenChargeBetheCandidateNormalized_hasEigenvalue_eq
  {s k : Nat} :
-- imply
  ∀ᶠ c : Real in atTop, Module.End.HasEigenvalue (Matrix.toEuclideanLin (sixVertexSectorTransferNormalized (sixVertexFourWidth (2 * s) k) (sixVertexFixedChargeBetheParticleCount (2 * s) k) c)) (sixVertexFixedEvenChargeBetheCandidateNormalized s k c) := by
-- proof
  apply StatMech.FrontierD.eventually_sixVertexFixedEvenChargeBetheCandidateNormalized_hasEigenvalue s k

/--
[eventually_sixVertexFixedOddChargeBetheCandidateNormalized_hasEigenvalue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeSpectralBranch.lean)
-/
@[path]
private lemma eventually_sixVertexFixedOddChargeBetheCandidateNormalized_hasEigenvalue_eq
  {s k : Nat} :
-- imply
  ∀ᶠ c : Real in atTop, Module.End.HasEigenvalue (Matrix.toEuclideanLin (sixVertexSectorTransferNormalized (sixVertexFourWidth (2 * s + 1) k) (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k) c)) (sixVertexFixedOddChargeBetheCandidateNormalized s k c) := by
-- proof
  apply StatMech.FrontierD.eventually_sixVertexFixedOddChargeBetheCandidateNormalized_hasEigenvalue s k


-- created on 2026-10-23
