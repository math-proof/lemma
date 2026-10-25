import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusSquareCrossing.Part6
open SimpleGraph Set StatMech StatMech.BeffaraDC


/--
[torusCoordSwap_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusSquareCrossing.lean)
-/
@[path]
private lemma torusCoordSwap_apply_eq
  {L : ℕ}
  {x : ZMod L × ZMod L} :
-- imply
  torusCoordSwap L x = (x.2, x.1) := by
-- proof
  apply StatMech.BeffaraDC.torusCoordSwap_apply L x

/--
[torusCoordSwap_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusSquareCrossing.lean)
-/
@[path]
private lemma torusCoordSwap_symm_eq
  {L : ℕ} :
-- imply
  (torusCoordSwap L).symm = torusCoordSwap L := by
-- proof
  apply StatMech.BeffaraDC.torusCoordSwap_symm L

/--
[onsTorusGraph_adj_coordSwap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusSquareCrossing.lean)
-/
@[path]
private lemma onsTorusGraph_adj_coordSwap_eq
  {L : ℕ}
  [Fact (2 < L)]
  {x y : ZMod L × ZMod L} :
-- imply
  (onsTorusGraph L).Adj (torusCoordSwap L x) (torusCoordSwap L y) ↔ (onsTorusGraph L).Adj x y := by
-- proof
  apply StatMech.BeffaraDC.onsTorusGraph_adj_coordSwap L x y

/--
[torusCoordSwap_mem_edgeFinset_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusSquareCrossing.lean)
-/
@[path]
private lemma torusCoordSwap_mem_edgeFinset_iff_eq
  {L : ℕ}
  [Fact (2 < L)]
  {e : Sym2 (ZMod L × ZMod L)} :
-- imply
  Sym2.map (torusCoordSwap L) e ∈ (onsTorusGraph L).edgeFinset ↔ e ∈ (onsTorusGraph L).edgeFinset := by
-- proof
  apply StatMech.BeffaraDC.torusCoordSwap_mem_edgeFinset_iff L e

/--
[torusAmbientConfigExtend_swap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusSquareCrossing.lean)
-/
@[path]
private lemma torusAmbientConfigExtend_swap_eq
  {L : ℕ}
  [Fact (2 < L)]
  {omega : TorusAmbientConfig L} :
-- imply
  torusAmbientConfigExtend L (torusAmbientSwapConfig L omega) = FK.reCfgIso (torusCoordSwap L) (torusAmbientConfigExtend L omega) := by
-- proof
  apply StatMech.BeffaraDC.torusAmbientConfigExtend_swap L omega

/--
[torusAmbientFKWeight_swap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusSquareCrossing.lean)
-/
@[path]
private lemma torusAmbientFKWeight_swap_eq
  {L : ℕ}
  [Fact (2 < L)]
  {p q : ℝ}
  {omega : TorusAmbientConfig L} :
-- imply
  torusAmbientFKWeight L p q (torusAmbientSwapConfig L omega) = torusAmbientFKWeight L p q omega := by
-- proof
  apply StatMech.BeffaraDC.torusAmbientFKWeight_swap L p q omega

/--
[torusAmbientProbability_swap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusSquareCrossing.lean)
-/
@[path]
private lemma torusAmbientProbability_swap_eq
  {L : ℕ}
  [Fact (2 < L)]
  {p q : ℝ}
  {omega : TorusAmbientConfig L} :
-- imply
  torusAmbientProbability L p q (torusAmbientSwapConfig L omega) = torusAmbientProbability L p q omega := by
-- proof
  apply StatMech.BeffaraDC.torusAmbientProbability_swap L p q omega

/--
[mem_torusAmbientRotatedEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusSquareCrossing.lean)
-/
@[path]
private lemma mem_torusAmbientRotatedEvent_eq
  {L : ℕ}
  [Fact (2 < L)]
  {A : Finset (TorusAmbientConfig L)}
  {omega : TorusAmbientConfig L} :
-- imply
  omega ∈ torusAmbientRotatedEvent L A ↔ torusAmbientSwapConfig L omega ∈ A := by
-- proof
  apply StatMech.BeffaraDC.mem_torusAmbientRotatedEvent L

/--
[torusAmbientEventProbability_rotated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusSquareCrossing.lean)
-/
@[path]
private lemma torusAmbientEventProbability_rotated_eq
  {L : ℕ}
  [Fact (2 < L)]
  {p q : ℝ}
  {A : Finset (TorusAmbientConfig L)} :
-- imply
  torusAmbientEventProbability L p q (torusAmbientRotatedEvent L A) = torusAmbientEventProbability L p q A := by
-- proof
  apply StatMech.BeffaraDC.torusAmbientEventProbability_rotated L p q A

/--
[mem_torusAmbientDualPullbackEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusSquareCrossing.lean)
-/
@[path]
private lemma mem_torusAmbientDualPullbackEvent_eq
  {L : ℕ}
  [Fact (2 < L)]
  {A : Finset (TorusAmbientConfig L)}
  {omega : TorusAmbientConfig L} :
-- imply
  omega ∈ torusAmbientDualPullbackEvent L A ↔ torusCellDualAmbientConfig L omega ∈ A := by
-- proof
  apply StatMech.BeffaraDC.mem_torusAmbientDualPullbackEvent L

/--
[torusAmbientProbability_le_q_mul_dual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusSquareCrossing.lean)
-/
@[path]
private lemma torusAmbientProbability_le_q_mul_dual_eq
  {L : ℕ}
  [Fact (2 < L)]
  {omega : TorusAmbientConfig L}
  {q : ℝ}
-- given
  (hq1 : 1 ≤ q) :
-- imply
  torusAmbientProbability L (selfDualPoint q) q omega ≤ q * torusAmbientProbability L (selfDualPoint q) q (torusCellDualAmbientConfig L omega) := by
-- proof
  apply StatMech.BeffaraDC.torusAmbientProbability_le_q_mul_dual L omega hq1

/--
[torusAmbientDualPullbackEventProbability_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusSquareCrossing.lean)
-/
@[path]
private lemma torusAmbientDualPullbackEventProbability_le_eq
  {L : ℕ}
  [Fact (2 < L)]
  {A : Finset (TorusAmbientConfig L)}
  {q : ℝ}
-- given
  (hq1 : 1 ≤ q) :
-- imply
  torusAmbientEventProbability L (selfDualPoint q) q (torusAmbientDualPullbackEvent L A) ≤ q * torusAmbientEventProbability L (selfDualPoint q) q A := by
-- proof
  apply StatMech.BeffaraDC.torusAmbientDualPullbackEventProbability_le L A hq1

/--
[mem_torusSquareHorizontalCrossingEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusSquareCrossing.lean)
-/
@[path]
private lemma mem_torusSquareHorizontalCrossingEvent_eq
  {L : ℕ}
  [Fact (2 < L)]
  {n : ℕ}
  {omega : TorusAmbientConfig L} :
-- imply
  omega ∈ torusSquareHorizontalCrossingEvent L n ↔ torusSquareHorizontalCrossing L n omega := by
-- proof
  apply StatMech.BeffaraDC.mem_torusSquareHorizontalCrossingEvent L n omega

/--
[mem_torusSquareVerticalCrossingEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusSquareCrossing.lean)
-/
@[path]
private lemma mem_torusSquareVerticalCrossingEvent_eq
  {L : ℕ}
  [Fact (2 < L)]
  {n : ℕ}
  {omega : TorusAmbientConfig L} :
-- imply
  omega ∈ torusSquareVerticalCrossingEvent L n ↔ torusSquareHorizontalCrossing L n (torusAmbientSwapConfig L omega) := by
-- proof
  apply StatMech.BeffaraDC.mem_torusSquareVerticalCrossingEvent L n omega

/--
[torus_squareCrossing_ge_one_div_one_add_q](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusSquareCrossing.lean)
-/
@[path]
private lemma torus_squareCrossing_ge_one_div_one_add_q_eq
  {L : ℕ}
  [Fact (2 < L)]
  {q : ℝ}
-- given
  (horizontal : Finset (TorusAmbientConfig L))
  (hq1 : 1 ≤ q)
  (hdualCrossing : ∀ omega : TorusAmbientConfig L, omega ∉ horizontal ↔ torusCellDualAmbientConfig L omega ∈ torusAmbientRotatedEvent L horizontal) :
-- imply
  1 / (1 + q) ≤ torusAmbientEventProbability L (selfDualPoint q) q horizontal := by
-- proof
  apply StatMech.BeffaraDC.torus_squareCrossing_ge_one_div_one_add_q L horizontal hq1 hdualCrossing

/--
[torus_concreteSquareCrossing_ge_one_div_one_add_q](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusSquareCrossing.lean)
-/
@[path]
private lemma torus_concreteSquareCrossing_ge_one_div_one_add_q_eq
  {L : ℕ}
  [Fact (2 < L)]
  {n : ℕ}
  {q : ℝ}
-- given
  (_hn : 1 ≤ n)
  (_hnL : n < L)
  (hq1 : 1 ≤ q)
  (hdualCrossing : ∀ omega : TorusAmbientConfig L, ¬ torusSquareHorizontalCrossing L n omega ↔ torusCellDualAmbientConfig L omega ∈ torusSquareVerticalCrossingEvent L n) :
-- imply
  1 / (1 + q) ≤ torusAmbientEventProbability L (selfDualPoint q) q (torusSquareHorizontalCrossingEvent L n) := by
-- proof
  apply StatMech.BeffaraDC.torus_concreteSquareCrossing_ge_one_div_one_add_q L n _hn _hnL hq1 hdualCrossing

/--
[torus_squareCrossing_const_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusSquareCrossing.lean)
-/
@[path]
private lemma torus_squareCrossing_const_pos_eq
  {q : ℝ}
-- given
  (hq1 : 1 ≤ q) :
-- imply
  0 < 1 / (1 + q) := by
-- proof
  apply StatMech.BeffaraDC.torus_squareCrossing_const_pos hq1


-- created on 2026-10-23
