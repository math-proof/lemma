import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.SLE.BrownianDyadicControl.Part3
open Filter MeasureTheory ProbabilityTheory Set StatMech StatMech.SLE


/--
[brownianDyadicDenominator_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianDyadicControl.lean)
-/
@[path]
private lemma brownianDyadicDenominator_pos_eq
  {n : Nat} :
-- imply
  0 < brownianDyadicDenominator n := by
-- proof
  apply StatMech.SLE.brownianDyadicDenominator_pos n

/--
[brownianDyadicPoint_succ_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianDyadicControl.lean)
-/
@[path]
private lemma brownianDyadicPoint_succ_sub_eq
  {N n k : Nat} :
-- imply
  brownianDyadicPoint N n (k + 1) - brownianDyadicPoint N n k = ((brownianDyadicDenominator n : Nat) : Real)⁻¹ := by
-- proof
  apply StatMech.SLE.brownianDyadicPoint_succ_sub N n k

/--
[edist_brownianDyadicPoint_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianDyadicControl.lean)
-/
@[path]
private lemma edist_brownianDyadicPoint_succ_eq
  {N n k : Nat} :
-- imply
  edist (brownianDyadicPoint N n k) (brownianDyadicPoint N n (k + 1)) = ((brownianDyadicDenominator n : Nat) : ENNReal)⁻¹ := by
-- proof
  apply StatMech.SLE.edist_brownianDyadicPoint_succ N n k

/--
[brownianProductLaw_brownianDyadicEdgeBadEvent_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianDyadicControl.lean)
-/
@[path]
private lemma brownianProductLaw_brownianDyadicEdgeBadEvent_le_eq
  {N n k : Nat} :
-- imply
  brownianProductLaw (brownianDyadicEdgeBadEvent N n k) <= ((3 : NNReal) * (((brownianDyadicDenominator n : Nat) : ENNReal)⁻¹) ^ (2 : Real)) / (brownianDyadicThreshold n) ^ (4 : Nat) := by
-- proof
  apply StatMech.SLE.brownianProductLaw_brownianDyadicEdgeBadEvent_le N n k

/--
[brownianProductLaw_brownianDyadicBadEvent_le_raw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianDyadicControl.lean)
-/
@[path]
private lemma brownianProductLaw_brownianDyadicBadEvent_le_raw_eq
  {N n : Nat} :
-- imply
  brownianProductLaw (brownianDyadicBadEvent N n) <= (2 * N * brownianDyadicDenominator n : Nat) * (((3 : NNReal) * (((brownianDyadicDenominator n : Nat) : ENNReal)⁻¹) ^ (2 : Real)) / (brownianDyadicThreshold n) ^ (4 : Nat)) := by
-- proof
  apply StatMech.SLE.brownianProductLaw_brownianDyadicBadEvent_le_raw N n

/--
[brownianProductLaw_brownianDyadicBadEvent_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianDyadicControl.lean)
-/
@[path]
private lemma brownianProductLaw_brownianDyadicBadEvent_le_eq
  {N n : Nat} :
-- imply
  brownianProductLaw (brownianDyadicBadEvent N n) <= ((6 * N : Nat) : ENNReal) * ((16 : ENNReal)⁻¹) ^ n := by
-- proof
  apply StatMech.SLE.brownianProductLaw_brownianDyadicBadEvent_le N n

/--
[tsum_brownianProductLaw_brownianDyadicBadEvent_ne_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianDyadicControl.lean)
-/
@[path]
private lemma tsum_brownianProductLaw_brownianDyadicBadEvent_ne_top_eq
  {N : Nat} :
-- imply
  Ne (∑' n : Nat, brownianProductLaw (brownianDyadicBadEvent N n)) (⊤ : ENNReal) := by
-- proof
  apply StatMech.SLE.tsum_brownianProductLaw_brownianDyadicBadEvent_ne_top N

/--
[brownianCoordinateProcess_ae_eventually_dyadicEdge_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianDyadicControl.lean)
-/
@[path]
private lemma brownianCoordinateProcess_ae_eventually_dyadicEdge_lt_eq
  {N : Nat} :
-- imply
  ∀ᵐ omega ∂brownianProductLaw, ∀ᶠ n in atTop, ∀ k ∈ Finset.range (2 * N * brownianDyadicDenominator n), edist (brownianCoordinateProcess (brownianDyadicPoint N n k) omega) (brownianCoordinateProcess (brownianDyadicPoint N n (k + 1)) omega) < brownianDyadicThreshold n := by
-- proof
  apply StatMech.SLE.brownianCoordinateProcess_ae_eventually_dyadicEdge_lt N

/--
[brownianCoordinateProcess_ae_forall_eventually_dyadicEdge_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianDyadicControl.lean)
-/
@[path]
private lemma brownianCoordinateProcess_ae_forall_eventually_dyadicEdge_lt_eq :
-- imply
  ∀ᵐ omega ∂brownianProductLaw, ∀ N : Nat, ∀ᶠ n in atTop, ∀ k ∈ Finset.range (2 * N * brownianDyadicDenominator n), edist (brownianCoordinateProcess (brownianDyadicPoint N n k) omega) (brownianCoordinateProcess (brownianDyadicPoint N n (k + 1)) omega) < brownianDyadicThreshold n := by
-- proof
  apply StatMech.SLE.brownianCoordinateProcess_ae_forall_eventually_dyadicEdge_lt

/--
[edist_brownianCoordinateProcess_dyadicPoint_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianDyadicControl.lean)
-/
@[path]
private lemma edist_brownianCoordinateProcess_dyadicPoint_le_eq
  {N n a b : Nat}
-- given
  (omega : Real -> Real)
  (hedge : ∀ k ∈ Finset.range (2 * N * brownianDyadicDenominator n), edist (brownianCoordinateProcess (brownianDyadicPoint N n k) omega) (brownianCoordinateProcess (brownianDyadicPoint N n (k + 1)) omega) < brownianDyadicThreshold n)
  (hab : a <= b)
  (hb : b <= 2 * N * brownianDyadicDenominator n) :
-- imply
  edist (brownianCoordinateProcess (brownianDyadicPoint N n a) omega) (brownianCoordinateProcess (brownianDyadicPoint N n b) omega) <= (b - a : Nat) * brownianDyadicThreshold n := by
-- proof
  apply StatMech.SLE.edist_brownianCoordinateProcess_dyadicPoint_le omega N n a b hedge hab hb


-- created on 2026-10-23
