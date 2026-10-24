import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexBlockRepetition
open Finset StatMech StatMech.FrontierD


/--
[sixVertexRectangleTileBlocks_horizontal_castSucc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBlockRepetition.lean)
-/
@[path]
private lemma sixVertexRectangleTileBlocks_horizontal_castSucc_eq
  {N M a b : ℕ}
  {ξ : SixVertexToroidalBoundary N M}
  {ω : SixVertexRectangleBlockCopies ξ a b}
  {x : Fin (a + 1)}
  {y : Fin (b + 1)}
  {i : Fin N}
  {j : Fin M} :
-- imply
  (sixVertexRectangleTileBlocks ω).horizontal ((finProdFinEquiv (x, i)).castSucc, finProdFinEquiv (y, j)) = (ω (x, y)).1.horizontal (i.castSucc, j) := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleTileBlocks_horizontal_castSucc ω x y i j

/--
[sixVertexRectangleTileBlocks_vertical_castSucc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBlockRepetition.lean)
-/
@[path]
private lemma sixVertexRectangleTileBlocks_vertical_castSucc_eq
  {N M a b : ℕ}
  {ξ : SixVertexToroidalBoundary N M}
  {ω : SixVertexRectangleBlockCopies ξ a b}
  {x : Fin (a + 1)}
  {y : Fin (b + 1)}
  {i : Fin N}
  {j : Fin M} :
-- imply
  (sixVertexRectangleTileBlocks ω).vertical (finProdFinEquiv (x, i), (finProdFinEquiv (y, j)).castSucc) = (ω (x, y)).1.vertical (i, j.castSucc) := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleTileBlocks_vertical_castSucc ω x y i j

/--
[sixVertexRectangleTileBlocks_horizontal_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBlockRepetition.lean)
-/
@[path]
private lemma sixVertexRectangleTileBlocks_horizontal_succ_eq
  {N M a b : ℕ}
  {ξ : SixVertexToroidalBoundary (N + 1) M}
  {ω : SixVertexRectangleBlockCopies ξ a b}
  {x : Fin (a + 1)}
  {y : Fin (b + 1)}
  {i : Fin (N + 1)}
  {j : Fin M} :
-- imply
  (sixVertexRectangleTileBlocks ω).horizontal ((finProdFinEquiv (x, i)).succ, finProdFinEquiv (y, j)) = (ω (x, y)).1.horizontal (i.succ, j) := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleTileBlocks_horizontal_succ ω x y i j

/--
[sixVertexRectangleTileBlocks_vertical_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBlockRepetition.lean)
-/
@[path]
private lemma sixVertexRectangleTileBlocks_vertical_succ_eq
  {N M a b : ℕ}
  {ξ : SixVertexToroidalBoundary N (M + 1)}
  {ω : SixVertexRectangleBlockCopies ξ a b}
  {x : Fin (a + 1)}
  {y : Fin (b + 1)}
  {i : Fin N}
  {j : Fin (M + 1)} :
-- imply
  (sixVertexRectangleTileBlocks ω).vertical (finProdFinEquiv (x, i), (finProdFinEquiv (y, j)).succ) = (ω (x, y)).1.vertical (i, j.succ) := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleTileBlocks_vertical_succ ω x y i j

/--
[sixVertexRectangleTileBlocks_localWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBlockRepetition.lean)
-/
@[path]
private lemma sixVertexRectangleTileBlocks_localWeight_eq
  {N M a b : ℕ}
  {ξ : SixVertexToroidalBoundary (N + 1) (M + 1)}
  {c : ℝ}
  {ω : SixVertexRectangleBlockCopies ξ a b}
  {x : Fin (a + 1)}
  {y : Fin (b + 1)}
  {i : Fin (N + 1)}
  {j : Fin (M + 1)} :
-- imply
  (sixVertexRectangleTileBlocks ω).localWeight c (finProdFinEquiv (x, i), finProdFinEquiv (y, j)) = (ω (x, y)).1.localWeight c (i, j) := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleTileBlocks_localWeight c ω x y i j

/--
[sixVertexRectangleTileBlocks_weight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBlockRepetition.lean)
-/
@[path]
private lemma sixVertexRectangleTileBlocks_weight_eq
  {N M a b : ℕ}
  {ξ : SixVertexToroidalBoundary (N + 1) (M + 1)}
  {c : ℝ}
  {ω : SixVertexRectangleBlockCopies ξ a b} :
-- imply
  (sixVertexRectangleTileBlocks ω).weight c = ∏ xy : Fin (a + 1) × Fin (b + 1), (ω xy).1.weight c := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleTileBlocks_weight c ω

/--
[sixVertexRectangleTileBlocks_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBlockRepetition.lean)
-/
@[path]
private lemma sixVertexRectangleTileBlocks_boundary_eq
  {N M a b : ℕ}
  {ξ : SixVertexToroidalBoundary (N + 1) (M + 1)}
  {ω : SixVertexRectangleBlockCopies ξ a b} :
-- imply
  sixVertexRectangleBoundary (sixVertexRectangleTileBlocks ω) = sixVertexToroidalRectangleBoundary (sixVertexRepeatToroidalBoundary ξ) := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleTileBlocks_boundary ω

/--
[sixVertexRepeatToroidalBoundary_balanced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBlockRepetition.lean)
-/
@[path]
private lemma sixVertexRepeatToroidalBoundary_balanced_eq
  {N M a b : ℕ}
  {ξ : SixVertexToroidalBoundary N M}
-- given
  (hN : Even N)
  (hξ : ξ.Balanced) :
-- imply
  (sixVertexRepeatToroidalBoundary (a := a) (b := b) ξ).Balanced := by
-- proof
  apply StatMech.FrontierD.sixVertexRepeatToroidalBoundary_balanced hN ξ hξ

/--
[sixVertexRectangleTileBlocks_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBlockRepetition.lean)
-/
@[path]
private lemma sixVertexRectangleTileBlocks_injective_eq
  {N M a b : ℕ}
  {ξ : SixVertexToroidalBoundary (N + 1) (M + 1)} :
-- imply
  Function.Injective (sixVertexRectangleTileBlocks (ξ := ξ) : SixVertexRectangleBlockCopies ξ a b → SixVertexRectangleArrows ((a + 1) * (N + 1)) ((b + 1) * (M + 1))) := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleTileBlocks_injective

/--
[sixVertexRectangleTileBlocksBoundaryFiber_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBlockRepetition.lean)
-/
@[path]
private lemma sixVertexRectangleTileBlocksBoundaryFiber_injective_eq
  {N M a b : ℕ}
  {ξ : SixVertexToroidalBoundary (N + 1) (M + 1)} :
-- imply
  Function.Injective (sixVertexRectangleTileBlocksBoundaryFiber (ξ := ξ) (a := a) (b := b)) := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleTileBlocksBoundaryFiber_injective

/--
[sixVertexRectangleBoundaryPartitionSum_pow_blockCount_le_repeated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBlockRepetition.lean)
-/
@[path]
private lemma sixVertexRectangleBoundaryPartitionSum_pow_blockCount_le_repeated_eq
  {N M a b : ℕ}
  {c : ℝ}
  {ξ : SixVertexToroidalBoundary (N + 1) (M + 1)}
-- given
  (hc : 0 ≤ c) :
-- imply
  sixVertexRectangleBoundaryPartitionSum (N + 1) (M + 1) c (sixVertexToroidalRectangleBoundary ξ) ^ ((a + 1) * (b + 1)) ≤ sixVertexRectangleBoundaryPartitionSum ((a + 1) * (N + 1)) ((b + 1) * (M + 1)) c (sixVertexToroidalRectangleBoundary (sixVertexRepeatToroidalBoundary (a := a) (b := b) ξ)) := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleBoundaryPartitionSum_pow_blockCount_le_repeated hc ξ

/--
[sixVertexRectangleMaxBalancedBoundaryContribution_exists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBlockRepetition.lean)
-/
@[path]
private lemma sixVertexRectangleMaxBalancedBoundaryContribution_exists_eq
  {N M : ℕ}
  {c : ℝ} :
-- imply
  ∃ ξ : SixVertexToroidalBoundary N M, (if ξ.Balanced then sixVertexRectangleBoundaryPartitionSum N M c (sixVertexToroidalRectangleBoundary ξ) else 0) = sixVertexRectangleMaxBalancedBoundaryContribution N M c := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleMaxBalancedBoundaryContribution_exists N M c

/--
[sixVertexRectangleMaxBalancedBoundaryContribution_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBlockRepetition.lean)
-/
@[path]
private lemma sixVertexRectangleMaxBalancedBoundaryContribution_nonneg_eq
  {N M : ℕ}
  {c : ℝ}
-- given
  (hc : 0 ≤ c) :
-- imply
  0 ≤ sixVertexRectangleMaxBalancedBoundaryContribution N M c := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleMaxBalancedBoundaryContribution_nonneg N M hc

/--
[sixVertexRectangleBalancedPartitionSum_le_card_mul_maxBalanced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBlockRepetition.lean)
-/
@[path]
private lemma sixVertexRectangleBalancedPartitionSum_le_card_mul_maxBalanced_eq
  {N M : ℕ}
  {c : ℝ} :
-- imply
  sixVertexRectangleBalancedPartitionSum N M c ≤ (2 : ℝ) ^ (N + M) * sixVertexRectangleMaxBalancedBoundaryContribution N M c := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleBalancedPartitionSum_le_card_mul_maxBalanced N M c

/--
[sixVertexRectangleBalancedPartitionSum_pow_blockCount_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBlockRepetition.lean)
-/
@[path]
private lemma sixVertexRectangleBalancedPartitionSum_pow_blockCount_le_eq
  {N M a b : ℕ}
  {c : ℝ}
-- given
  (hc : 0 ≤ c)
  (hN : Even (N + 1)) :
-- imply
  sixVertexRectangleBalancedPartitionSum (N + 1) (M + 1) c ^ ((a + 1) * (b + 1)) ≤ ((2 : ℝ) ^ ((N + 1) + (M + 1))) ^ ((a + 1) * (b + 1)) * sixVertexRectangleBalancedPartitionSum ((a + 1) * (N + 1)) ((b + 1) * (M + 1)) c := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleBalancedPartitionSum_pow_blockCount_le hc hN

/--
[sixVertexRectangleStraightExtend_horizontal_castSucc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBlockRepetition.lean)
-/
@[path]
private lemma sixVertexRectangleStraightExtend_horizontal_castSucc_eq
  {N M r q : ℕ}
  {z : Fin r → Bool}
  {ω : SixVertexRectangleArrows N M}
  {i : Fin N}
  {j : Fin M} :
-- imply
  (sixVertexRectangleStraightExtend (q := q) z ω).horizontal ((Fin.castAdd r i).castSucc, Fin.castAdd q j) = ω.horizontal (i.castSucc, j) := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleStraightExtend_horizontal_castSucc z ω i j

/--
[sixVertexRectangleStraightExtend_horizontal_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBlockRepetition.lean)
-/
@[path]
private lemma sixVertexRectangleStraightExtend_horizontal_succ_eq
  {N M r q : ℕ}
  {z : Fin r → Bool}
  {ω : SixVertexRectangleArrows (N + 1) M}
  {i : Fin (N + 1)}
  {j : Fin M} :
-- imply
  (sixVertexRectangleStraightExtend (q := q) z ω).horizontal ((Fin.castAdd r i).succ, Fin.castAdd q j) = ω.horizontal (i.succ, j) := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleStraightExtend_horizontal_succ z ω i j

/--
[sixVertexRectangleStraightExtend_vertical_castSucc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBlockRepetition.lean)
-/
@[path]
private lemma sixVertexRectangleStraightExtend_vertical_castSucc_eq
  {N M r q : ℕ}
  {z : Fin r → Bool}
  {ω : SixVertexRectangleArrows N M}
  {i : Fin N}
  {j : Fin M} :
-- imply
  (sixVertexRectangleStraightExtend (q := q) z ω).vertical (Fin.castAdd r i, (Fin.castAdd q j).castSucc) = ω.vertical (i, j.castSucc) := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleStraightExtend_vertical_castSucc z ω i j

/--
[sixVertexRectangleStraightExtend_vertical_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBlockRepetition.lean)
-/
@[path]
private lemma sixVertexRectangleStraightExtend_vertical_succ_eq
  {N M r q : ℕ}
  {z : Fin r → Bool}
  {ω : SixVertexRectangleArrows N (M + 1)}
  {i : Fin N}
  {j : Fin (M + 1)} :
-- imply
  (sixVertexRectangleStraightExtend (q := q) z ω).vertical (Fin.castAdd r i, (Fin.castAdd q j).succ) = ω.vertical (i, j.succ) := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleStraightExtend_vertical_succ z ω i j

/--
[sixVertexRectangleStraightExtend_localWeight_base](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBlockRepetition.lean)
-/
@[path]
private lemma sixVertexRectangleStraightExtend_localWeight_base_eq
  {N M r q : ℕ}
  {c : ℝ}
  {z : Fin r → Bool}
  {ω : SixVertexRectangleArrows (N + 1) (M + 1)}
  {i : Fin (N + 1)}
  {j : Fin (M + 1)} :
-- imply
  (sixVertexRectangleStraightExtend z ω).localWeight c (Fin.castAdd r i, Fin.castAdd q j) = ω.localWeight c (i, j) := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleStraightExtend_localWeight_base c z ω i j

/--
[sixVertexRectangleStraightExtend_localWeight_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBlockRepetition.lean)
-/
@[path]
private lemma sixVertexRectangleStraightExtend_localWeight_right_eq
  {N M r q : ℕ}
  {c : ℝ}
  {z : Fin r → Bool}
  {ω : SixVertexRectangleArrows (N + 1) (M + 1)}
  {i : Fin r}
  {j : Fin (M + 1)} :
-- imply
  (sixVertexRectangleStraightExtend z ω).localWeight c (Fin.natAdd (N + 1) i, Fin.castAdd q j) = 1 := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleStraightExtend_localWeight_right c z ω i j

/--
[sixVertexRectangleStraightExtend_localWeight_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBlockRepetition.lean)
-/
@[path]
private lemma sixVertexRectangleStraightExtend_localWeight_top_eq
  {N M r q : ℕ}
  {c : ℝ}
  {z : Fin r → Bool}
  {ω : SixVertexRectangleArrows (N + 1) (M + 1)}
  {i : Fin ((N + 1) + r)}
  {j : Fin q} :
-- imply
  (sixVertexRectangleStraightExtend z ω).localWeight c (i, Fin.natAdd (M + 1) j) = 1 := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleStraightExtend_localWeight_top c z ω i j

/--
[sixVertexRectangleStraightExtend_weight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBlockRepetition.lean)
-/
@[path]
private lemma sixVertexRectangleStraightExtend_weight_eq
  {N M r q : ℕ}
  {c : ℝ}
  {z : Fin r → Bool}
  {ω : SixVertexRectangleArrows (N + 1) (M + 1)} :
-- imply
  (sixVertexRectangleStraightExtend (q := q) z ω).weight c = ω.weight c := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleStraightExtend_weight c z ω

/--
[sixVertexRectangleStraightExtend_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBlockRepetition.lean)
-/
@[path]
private lemma sixVertexRectangleStraightExtend_boundary_eq
  {N M r q : ℕ}
  {ξ : SixVertexToroidalBoundary (N + 1) (M + 1)}
  {z : Fin r → Bool}
  {ω : SixVertexRectangleBoundaryFiber (sixVertexToroidalRectangleBoundary ξ)} :
-- imply
  sixVertexRectangleBoundary (sixVertexRectangleStraightExtend z ω.1) = sixVertexToroidalRectangleBoundary (sixVertexStraightExtendedToroidalBoundary q ξ z) := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleStraightExtend_boundary z ω

/--
[sixVertexHalfFilledRow_upCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBlockRepetition.lean)
-/
@[path]
private lemma sixVertexHalfFilledRow_upCount_eq
  {r : ℕ} :
-- imply
  #{i | sixVertexHalfFilledRow r i} = r / 2 := by
-- proof
  apply StatMech.FrontierD.sixVertexHalfFilledRow_upCount r

/--
[sixVertexStraightExtendedToroidalBoundary_balanced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBlockRepetition.lean)
-/
@[path]
private lemma sixVertexStraightExtendedToroidalBoundary_balanced_eq
  {N M r : ℕ}
  {q : ℕ}
  {ξ : SixVertexToroidalBoundary N M}
-- given
  (hN : Even N)
  (hr : Even r)
  (hξ : ξ.Balanced) :
-- imply
  (sixVertexStraightExtendedToroidalBoundary q ξ (sixVertexHalfFilledRow r)).Balanced := by
-- proof
  apply StatMech.FrontierD.sixVertexStraightExtendedToroidalBoundary_balanced hN hr q ξ hξ

/--
[sixVertexRectangleStraightExtend_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBlockRepetition.lean)
-/
@[path]
private lemma sixVertexRectangleStraightExtend_injective_eq
  {N M r q : ℕ}
  {z : Fin r → Bool} :
-- imply
  Function.Injective (sixVertexRectangleStraightExtend (N := N + 1) (M := M + 1) (q := q) z) := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleStraightExtend_injective z

/--
[sixVertexRectangleStraightExtendBoundaryFiber_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBlockRepetition.lean)
-/
@[path]
private lemma sixVertexRectangleStraightExtendBoundaryFiber_injective_eq
  {N M r q : ℕ}
  {ξ : SixVertexToroidalBoundary (N + 1) (M + 1)}
  {z : Fin r → Bool} :
-- imply
  Function.Injective (sixVertexRectangleStraightExtendBoundaryFiber (q := q) (ξ := ξ) z) := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleStraightExtendBoundaryFiber_injective z

/--
[sixVertexRectangleBalancedPartitionSum_eq_fiberSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBlockRepetition.lean)
-/
@[path]
private lemma sixVertexRectangleBalancedPartitionSum_eq_fiberSum_eq
  {N M : ℕ}
  {c : ℝ} :
-- imply
  sixVertexRectangleBalancedPartitionSum N M c = ∑ ξω : SixVertexRectangleBalancedBoundaryFibers N M, ξω.2.1.weight c := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleBalancedPartitionSum_eq_fiberSum N M c

/--
[sixVertexRectangleStraightExtendBalancedFibers_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBlockRepetition.lean)
-/
@[path]
private lemma sixVertexRectangleStraightExtendBalancedFibers_injective_eq
  {N M r : ℕ}
  {q : ℕ}
-- given
  (hN : Even (N + 1))
  (hr : Even r) :
-- imply
  Function.Injective (sixVertexRectangleStraightExtendBalancedFibers (M := M) hN hr q) := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleStraightExtendBalancedFibers_injective hN hr q

/--
[sixVertexRectangleStraightExtendBalancedFibers_weight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBlockRepetition.lean)
-/
@[path]
private lemma sixVertexRectangleStraightExtendBalancedFibers_weight_eq
  {N M r : ℕ}
  {q : ℕ}
  {c : ℝ}
  {ξω : SixVertexRectangleBalancedBoundaryFibers (N + 1) (M + 1)}
-- given
  (hN : Even (N + 1))
  (hr : Even r) :
-- imply
  ((sixVertexRectangleStraightExtendBalancedFibers hN hr q ξω).2.1).weight c = ξω.2.1.weight c := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleStraightExtendBalancedFibers_weight hN hr q c ξω

/--
[sixVertexRectangleBalancedPartitionSum_le_straightExtend](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBlockRepetition.lean)
-/
@[path]
private lemma sixVertexRectangleBalancedPartitionSum_le_straightExtend_eq
  {N M r : ℕ}
  {c : ℝ}
  {q : ℕ}
-- given
  (hc : 0 ≤ c)
  (hN : Even (N + 1))
  (hr : Even r) :
-- imply
  sixVertexRectangleBalancedPartitionSum (N + 1) (M + 1) c ≤ sixVertexRectangleBalancedPartitionSum ((N + 1) + r) ((M + 1) + q) c := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleBalancedPartitionSum_le_straightExtend hc hN hr q

/--
[sixVertexRectangleBalancedPartitionSum_pow_mulFactors_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBlockRepetition.lean)
-/
@[path]
private lemma sixVertexRectangleBalancedPartitionSum_pow_mulFactors_le_eq
  {N M A B : ℕ}
  {c : ℝ}
-- given
  (hc : 0 ≤ c)
  (hN : 0 < N)
  (hM : 0 < M)
  (hNeven : Even N)
  (hA : 0 < A)
  (hB : 0 < B) :
-- imply
  sixVertexRectangleBalancedPartitionSum N M c ^ (A * B) ≤ ((2 : ℝ) ^ (N + M)) ^ (A * B) * sixVertexRectangleBalancedPartitionSum (A * N) (B * M) c := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleBalancedPartitionSum_pow_mulFactors_le hc hN hM hNeven hA hB

/--
[sixVertexRectangleBalancedPartitionSum_le_straightExtend_general](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBlockRepetition.lean)
-/
@[path]
private lemma sixVertexRectangleBalancedPartitionSum_le_straightExtend_general_eq
  {N M r q : ℕ}
  {c : ℝ}
-- given
  (hc : 0 ≤ c)
  (hN : 0 < N)
  (hM : 0 < M)
  (hNeven : Even N)
  (hr : Even r) :
-- imply
  sixVertexRectangleBalancedPartitionSum N M c ≤ sixVertexRectangleBalancedPartitionSum (N + r) (M + q) c := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleBalancedPartitionSum_le_straightExtend_general hc hN hM hNeven hr

/--
[sixVertexRectangleBalancedPartitionSum_blockRepetition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBlockRepetition.lean)
-/
@[path]
private lemma sixVertexRectangleBalancedPartitionSum_blockRepetition_eq
  {N M n m : ℕ}
  {c : ℝ}
-- given
  (hc : 0 ≤ c)
  (hN : 0 < N)
  (hM : 0 < M)
  (hNeven : Even N)
  (hn : N < n)
  (hm : M < m)
  (hneven : Even n) :
-- imply
  sixVertexRectangleBalancedPartitionSum N M c ^ ((n / N) * (m / M)) ≤ ((2 : ℝ) ^ (N + M)) ^ ((n / N) * (m / M)) * sixVertexRectangleBalancedPartitionSum n m c := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleBalancedPartitionSum_blockRepetition hc hN hM hNeven hn hm hneven

/--
[sixVertexHalfFilledStraightBoundary_balanced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBlockRepetition.lean)
-/
@[path]
private lemma sixVertexHalfFilledStraightBoundary_balanced_eq
  {N M : ℕ} :
-- imply
  (sixVertexHalfFilledStraightBoundary N M).Balanced := by
-- proof
  apply StatMech.FrontierD.sixVertexHalfFilledStraightBoundary_balanced N M

/--
[sixVertexHalfFilledStraightRectangle_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBlockRepetition.lean)
-/
@[path]
private lemma sixVertexHalfFilledStraightRectangle_boundary_eq
  {N M : ℕ} :
-- imply
  sixVertexRectangleBoundary (sixVertexHalfFilledStraightRectangle N M) = sixVertexToroidalRectangleBoundary (sixVertexHalfFilledStraightBoundary N M) := by
-- proof
  apply StatMech.FrontierD.sixVertexHalfFilledStraightRectangle_boundary N M

/--
[sixVertexHalfFilledStraightRectangle_localWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBlockRepetition.lean)
-/
@[path]
private lemma sixVertexHalfFilledStraightRectangle_localWeight_eq
  {N M : ℕ}
  {c : ℝ}
  {v : Fin N × Fin M} :
-- imply
  (sixVertexHalfFilledStraightRectangle N M).localWeight c v = 1 := by
-- proof
  apply StatMech.FrontierD.sixVertexHalfFilledStraightRectangle_localWeight N M c v

/--
[sixVertexHalfFilledStraightRectangle_weight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBlockRepetition.lean)
-/
@[path]
private lemma sixVertexHalfFilledStraightRectangle_weight_eq
  {N M : ℕ}
  {c : ℝ} :
-- imply
  (sixVertexHalfFilledStraightRectangle N M).weight c = 1 := by
-- proof
  apply StatMech.FrontierD.sixVertexHalfFilledStraightRectangle_weight N M c

/--
[sixVertexRectangleBalancedPartitionSum_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBlockRepetition.lean)
-/
@[path]
private lemma sixVertexRectangleBalancedPartitionSum_pos_eq
  {N M : ℕ}
  {c : ℝ}
-- given
  (hc : 0 ≤ c) :
-- imply
  0 < sixVertexRectangleBalancedPartitionSum N M c := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleBalancedPartitionSum_pos N M hc

/--
[sixVertexRectangleBalancedPartitionSum_log_blockRepetition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBlockRepetition.lean)
-/
@[path]
private lemma sixVertexRectangleBalancedPartitionSum_log_blockRepetition_eq
  {N M n m : ℕ}
  {c : ℝ}
-- given
  (hc : 0 ≤ c)
  (hN : 0 < N)
  (hM : 0 < M)
  (hNeven : Even N)
  (hn : N < n)
  (hm : M < m)
  (hneven : Even n) :
-- imply
  (((n / N) * (m / M) : ℕ) : ℝ) * Real.log (sixVertexRectangleBalancedPartitionSum N M c) ≤ (((n / N) * (m / M) : ℕ) : ℝ) * (N + M : ℝ) * Real.log 2 + Real.log (sixVertexRectangleBalancedPartitionSum n m c) := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleBalancedPartitionSum_log_blockRepetition hc hN hM hNeven hn hm hneven

/--
[sixVertexRectangleBalancedDensity_blockRepetition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBlockRepetition.lean)
-/
@[path]
private lemma sixVertexRectangleBalancedDensity_blockRepetition_eq
  {N M n m : ℕ}
  {c : ℝ}
-- given
  (hc : 0 ≤ c)
  (hN : 0 < N)
  (hM : 0 < M)
  (hNeven : Even N)
  (hn : N < n)
  (hm : M < m)
  (hneven : Even n) :
-- imply
  ((((n / N) * (m / M) : ℕ) : ℝ) * (Real.log (sixVertexRectangleBalancedPartitionSum N M c) - (N + M : ℝ) * Real.log 2)) / ((n : ℝ) * (m : ℝ)) ≤ Real.log (sixVertexRectangleBalancedPartitionSum n m c) / ((n : ℝ) * (m : ℝ)) := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleBalancedDensity_blockRepetition hc hN hM hNeven hn hm hneven


-- created on 2026-10-23
