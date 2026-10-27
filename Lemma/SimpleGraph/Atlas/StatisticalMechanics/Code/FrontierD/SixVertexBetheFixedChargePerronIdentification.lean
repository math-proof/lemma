import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargePerronIdentification
open Finset Matrix StatMech StatMech.FrontierD


/--
[sixVertexFixedChargeLimitingRotatedActiveWave_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargePerronIdentification.lean)
-/
@[path]
private lemma sixVertexFixedChargeLimitingRotatedActiveWave_pos_eq
  {r k : Nat}
  {x : SixVertexNoAdjacentSector (sixVertexFourWidth r k) (sixVertexFixedChargeBetheParticleCount r k)} :
-- imply
  0 < sixVertexFixedChargeLimitingRotatedActiveWave r k x := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedChargeLimitingRotatedActiveWave_pos r k x

/--
[sixVertexNoAdjacentInfinity_eigenvalue_eq_top_of_positive_eigenvector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargePerronIdentification.lean)
-/
@[path]
private lemma sixVertexNoAdjacentInfinity_eigenvalue_eq_top_of_positive_eigenvector_eq
  {N n : Nat}
  {mu : Real}
  {q : SixVertexNoAdjacentSector N n → Real}
-- given
  (hn : 0 < n)
  (hhalf : 2 * n ≤ N)
  (hqpos : ∀ i, 0 < q i)
  (hq : sixVertexNoAdjacentTransferInfinity N n *ᵥ q = mu • q) :
-- imply
  mu = sixVertexNoAdjacentInfinityTopEigenvalue N n hn hhalf := by
-- proof
  apply StatMech.FrontierD.sixVertexNoAdjacentInfinity_eigenvalue_eq_top_of_positive_eigenvector hn hhalf q hqpos hq

/--
[sixVertexFixedEvenChargeBetheCandidateInfinity_eq_Perron](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargePerronIdentification.lean)
-/
@[path]
private lemma sixVertexFixedEvenChargeBetheCandidateInfinity_eq_Perron_eq
  {s k : Nat} :
-- imply
  sixVertexFixedEvenChargeBetheCandidateInfinity s k = sixVertexNoAdjacentInfinityTopEigenvalue (sixVertexFourWidth (2 * s) k) (sixVertexFixedChargeBetheParticleCount (2 * s) k) (sixVertexFixedChargeBetheParticleCount_pos (2 * s) k) (sixVertexFixedChargeBetheParticleCount_twice_le (2 * s) k) := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedEvenChargeBetheCandidateInfinity_eq_Perron s k

/--
[sixVertexFixedOddChargeBetheCandidateInfinity_eq_Perron](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargePerronIdentification.lean)
-/
@[path]
private lemma sixVertexFixedOddChargeBetheCandidateInfinity_eq_Perron_eq
  {s k : Nat} :
-- imply
  sixVertexFixedOddChargeBetheCandidateInfinity s k = sixVertexNoAdjacentInfinityTopEigenvalue (sixVertexFourWidth (2 * s + 1) k) (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k) (sixVertexFixedChargeBetheParticleCount_pos (2 * s + 1) k) (sixVertexFixedChargeBetheParticleCount_twice_le (2 * s + 1) k) := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedOddChargeBetheCandidateInfinity_eq_Perron s k


-- created on 2026-10-23
