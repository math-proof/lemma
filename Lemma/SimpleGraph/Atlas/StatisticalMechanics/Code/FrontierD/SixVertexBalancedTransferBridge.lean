import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBalancedTransferBridge.Part10
open Finset Matrix StatMech StatMech.FrontierD


/--
[svRowPrefixCount_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedTransferBridge.lean)
-/
@[path]
private lemma svRowPrefixCount_zero_eq
  {N : Nat}
  {x : SixVertexRow (N + 1)} :
-- imply
  svRowPrefixCount x 0 = (x 0).toNat := by
-- proof
  apply StatMech.FrontierD.svRowPrefixCount_zero x

/--
[svRowPrefixCount_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedTransferBridge.lean)
-/
@[path]
private lemma svRowPrefixCount_succ_eq
  {N : Nat}
  {x : SixVertexRow (N + 1)}
  {i : Fin N} :
-- imply
  svRowPrefixCount x i.succ = svRowPrefixCount x i.castSucc + (x i.succ).toNat := by
-- proof
  apply StatMech.FrontierD.svRowPrefixCount_succ x i

/--
[svRowPrefixCount_last](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedTransferBridge.lean)
-/
@[path]
private lemma svRowPrefixCount_last_eq
  {N : Nat}
  {x : SixVertexRow (N + 1)} :
-- imply
  svRowPrefixCount x (Fin.last N) = sixVertexUpCount x := by
-- proof
  apply StatMech.FrontierD.svRowPrefixCount_last x

/--
[svHorizontalIce_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedTransferBridge.lean)
-/
@[path]
private lemma svHorizontalIce_step_eq
  {N : Nat}
  {x y h : SixVertexRow N}
  {i : Fin N}
-- given
  (hN : 0 < N)
  (hice : svHorizontalIce hN x y h) :
-- imply
  (h i).toNat + (y i).toNat = (h (SixVertexArrows.cyclicPred hN i)).toNat + (x i).toNat := by
-- proof
  apply StatMech.FrontierD.svHorizontalIce_step hN hice i

/--
[svHorizontalIce_prefix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedTransferBridge.lean)
-/
@[path]
private lemma svHorizontalIce_prefix_eq
  {N : Nat}
  {x y h : SixVertexRow N}
  {k : Fin N}
-- given
  (hN : 0 < N)
  (hice : svHorizontalIce hN x y h) :
-- imply
  (h k).toNat + svRowPrefixCount y k = (h (svFinLast hN)).toNat + svRowPrefixCount x k := by
-- proof
  apply StatMech.FrontierD.svHorizontalIce_prefix hN hice k

/--
[svRowSectorAt_row](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedTransferBridge.lean)
-/
@[path]
private lemma svRowSectorAt_row_eq
  {N n : Nat}
  {x : SixVertexRow N}
-- given
  (hx : sixVertexUpCount x = n) :
-- imply
  sixVertexSectorRow (svRowSectorAt x hx) = x := by
-- proof
  apply StatMech.FrontierD.svRowSectorAt_row x hx

/--
[svRowPrefixCount_eq_sector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedTransferBridge.lean)
-/
@[path]
private lemma svRowPrefixCount_eq_sector_eq
  {N n : Nat}
  {x : SixVertexRow N}
  {k : Fin N}
-- given
  (hx : sixVertexUpCount x = n) :
-- imply
  svRowPrefixCount x k = sixVertexSectorPrefixCount (svRowSectorAt x hx) k := by
-- proof
  apply StatMech.FrontierD.svRowPrefixCount_eq_sector x hx k

/--
[svForwardInterlaced_iff_prefix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedTransferBridge.lean)
-/
@[path]
private lemma svForwardInterlaced_iff_prefix_eq
  {N : Nat}
  {x y : SixVertexRow N}
-- given
  (hcount : sixVertexUpCount x = sixVertexUpCount y) :
-- imply
  SixVertexForwardInterlaced x y ↔ svRowPrefixForward x y := by
-- proof
  apply StatMech.FrontierD.svForwardInterlaced_iff_prefix x y hcount

/--
[svCyclicPred_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedTransferBridge.lean)
-/
@[path]
private lemma svCyclicPred_zero_eq
  {N : Nat}
-- given
  (hN : 0 < N) :
-- imply
  SixVertexArrows.cyclicPred hN (⟨0, hN⟩ : Fin N) = svFinLast hN := by
-- proof
  apply StatMech.FrontierD.svCyclicPred_zero hN

/--
[svCyclicPred_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedTransferBridge.lean)
-/
@[path]
private lemma svCyclicPred_succ_eq
  {N : Nat}
  {i : Fin N} :
-- imply
  SixVertexArrows.cyclicPred (Nat.succ_pos N) i.succ = i.castSucc := by
-- proof
  apply StatMech.FrontierD.svCyclicPred_succ i

/--
[svHorizontalIce_iff_prefixRelation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedTransferBridge.lean)
-/
@[path]
private lemma svHorizontalIce_iff_prefixRelation_eq
  {N : Nat}
-- given
  (hN : 0 < N)
  (x y h : SixVertexRow N) :
-- imply
  svHorizontalIce hN x y h ↔ svHorizontalPrefixRelation hN x y h := by
-- proof
  apply StatMech.FrontierD.svHorizontalIce_iff_prefixRelation hN x y h

/--
[svForwardHorizontal_relation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedTransferBridge.lean)
-/
@[path]
private lemma svForwardHorizontal_relation_eq
  {N : Nat}
  {x y : SixVertexRow N}
-- given
  (hN : 0 < N)
  (hcount : sixVertexUpCount x = sixVertexUpCount y)
  (hpref : svRowPrefixForward x y) :
-- imply
  svHorizontalPrefixRelation hN x y (svForwardHorizontal x y) := by
-- proof
  apply StatMech.FrontierD.svForwardHorizontal_relation hN x y hcount hpref

/--
[svBackwardHorizontal_relation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedTransferBridge.lean)
-/
@[path]
private lemma svBackwardHorizontal_relation_eq
  {N : Nat}
  {x y : SixVertexRow N}
-- given
  (hN : 0 < N)
  (hcount : sixVertexUpCount x = sixVertexUpCount y)
  (hpref : svRowPrefixForward y x) :
-- imply
  svHorizontalPrefixRelation hN x y (svBackwardHorizontal x y) := by
-- proof
  apply StatMech.FrontierD.svBackwardHorizontal_relation hN x y hcount hpref

/--
[svForwardHorizontal_ice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedTransferBridge.lean)
-/
@[path]
private lemma svForwardHorizontal_ice_eq
  {N : Nat}
  {x y : SixVertexRow N}
-- given
  (hN : 0 < N)
  (hcount : sixVertexUpCount x = sixVertexUpCount y)
  (hpref : svRowPrefixForward x y) :
-- imply
  svHorizontalIce hN x y (svForwardHorizontal x y) := by
-- proof
  apply StatMech.FrontierD.svForwardHorizontal_ice hN x y hcount hpref

/--
[svBackwardHorizontal_ice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedTransferBridge.lean)
-/
@[path]
private lemma svBackwardHorizontal_ice_eq
  {N : Nat}
  {x y : SixVertexRow N}
-- given
  (hN : 0 < N)
  (hcount : sixVertexUpCount x = sixVertexUpCount y)
  (hpref : svRowPrefixForward y x) :
-- imply
  svHorizontalIce hN x y (svBackwardHorizontal x y) := by
-- proof
  apply StatMech.FrontierD.svBackwardHorizontal_ice hN x y hcount hpref

/--
[svRowPrefixCount_finLast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedTransferBridge.lean)
-/
@[path]
private lemma svRowPrefixCount_finLast_eq
  {N : Nat}
  {x : SixVertexRow N}
-- given
  (hN : 0 < N) :
-- imply
  svRowPrefixCount x (svFinLast hN) = sixVertexUpCount x := by
-- proof
  apply StatMech.FrontierD.svRowPrefixCount_finLast hN x

/--
[svHorizontalIce_upCount_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedTransferBridge.lean)
-/
@[path]
private lemma svHorizontalIce_upCount_eq_eq
  {N : Nat}
  {x y h : SixVertexRow N}
-- given
  (hN : 0 < N)
  (hice : svHorizontalIce hN x y h) :
-- imply
  sixVertexUpCount x = sixVertexUpCount y := by
-- proof
  apply StatMech.FrontierD.svHorizontalIce_upCount_eq hN hice

/--
[svHorizontalIce_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedTransferBridge.lean)
-/
@[path]
private lemma svHorizontalIce_cases_eq
  {N : Nat}
  {x y h : SixVertexRow N}
-- given
  (hN : 0 < N)
  (hice : svHorizontalIce hN x y h) :
-- imply
  (h (svFinLast hN) = false ∧ svRowPrefixForward x y ∧ h = svForwardHorizontal x y) ∨ (h (svFinLast hN) = true ∧ svRowPrefixForward y x ∧ h = svBackwardHorizontal x y) := by
-- proof
  apply StatMech.FrontierD.svHorizontalIce_cases hN hice

/--
[svRow_eq_of_prefixCount_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedTransferBridge.lean)
-/
@[path]
private lemma svRow_eq_of_prefixCount_eq_eq
  {N : Nat}
  {x y : SixVertexRow N}
-- given
  (hprefix : ∀ k, svRowPrefixCount x k = svRowPrefixCount y k) :
-- imply
  x = y := by
-- proof
  apply StatMech.FrontierD.svRow_eq_of_prefixCount_eq hprefix

/--
[svRowPrefixForward_antisymm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedTransferBridge.lean)
-/
@[path]
private lemma svRowPrefixForward_antisymm_eq
  {N : Nat}
  {x y : SixVertexRow N}
-- given
  (hxy : svRowPrefixForward x y)
  (hyx : svRowPrefixForward y x) :
-- imply
  x = y := by
-- proof
  apply StatMech.FrontierD.svRowPrefixForward_antisymm hxy hyx

/--
[svForwardHorizontal_last](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedTransferBridge.lean)
-/
@[path]
private lemma svForwardHorizontal_last_eq
  {N : Nat}
  {x y : SixVertexRow N}
-- given
  (hN : 0 < N)
  (hcount : sixVertexUpCount x = sixVertexUpCount y) :
-- imply
  svForwardHorizontal x y (svFinLast hN) = false := by
-- proof
  apply StatMech.FrontierD.svForwardHorizontal_last hN x y hcount

/--
[svBackwardHorizontal_last](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedTransferBridge.lean)
-/
@[path]
private lemma svBackwardHorizontal_last_eq
  {N : Nat}
  {x y : SixVertexRow N}
-- given
  (hN : 0 < N)
  (hcount : sixVertexUpCount x = sixVertexUpCount y) :
-- imply
  svBackwardHorizontal x y (svFinLast hN) = true := by
-- proof
  apply StatMech.FrontierD.svBackwardHorizontal_last hN x y hcount

/--
[svHorizontalOfBool_ice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedTransferBridge.lean)
-/
@[path]
private lemma svHorizontalOfBool_ice_eq
  {N : Nat}
  {x y : SixVertexRow N}
  {b : Bool}
-- given
  (hN : 0 < N)
  (hcount : sixVertexUpCount x = sixVertexUpCount y)
  (hb : if b then svRowPrefixForward y x else svRowPrefixForward x y) :
-- imply
  svHorizontalIce hN x y (svHorizontalOfBool x y b) := by
-- proof
  apply StatMech.FrontierD.svHorizontalOfBool_ice hN x y hcount b hb

/--
[svHorizontalIsC_iff_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedTransferBridge.lean)
-/
@[path]
private lemma svHorizontalIsC_iff_ne_eq
  {N : Nat}
  {x y h : SixVertexRow N}
  {i : Fin N}
-- given
  (hN : 0 < N)
  (hice : svHorizontalIce hN x y h) :
-- imply
  svHorizontalIsC hN h i ↔ x i ≠ y i := by
-- proof
  apply StatMech.FrontierD.svHorizontalIsC_iff_ne hN hice i

/--
[svHorizontalLocalWeight_of_ice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedTransferBridge.lean)
-/
@[path]
private lemma svHorizontalLocalWeight_of_ice_eq
  {N : Nat}
  {c : Real}
  {x y h : SixVertexRow N}
  {i : Fin N}
-- given
  (hN : 0 < N)
  (hice : svHorizontalIce hN x y h) :
-- imply
  svHorizontalLocalWeight hN c x y h i = if x i ≠ y i then c else 1 := by
-- proof
  apply StatMech.FrontierD.svHorizontalLocalWeight_of_ice hN c hice i

/--
[svHorizontalRowWeight_of_ice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedTransferBridge.lean)
-/
@[path]
private lemma svHorizontalRowWeight_of_ice_eq
  {N : Nat}
  {c : Real}
  {x y h : SixVertexRow N}
-- given
  (hN : 0 < N)
  (hice : svHorizontalIce hN x y h) :
-- imply
  svHorizontalRowWeight hN c x y h = c ^ sixVertexRowDistance x y := by
-- proof
  apply StatMech.FrontierD.svHorizontalRowWeight_of_ice hN c hice

/--
[svHorizontalRowWeight_eq_zero_of_not_ice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedTransferBridge.lean)
-/
@[path]
private lemma svHorizontalRowWeight_eq_zero_of_not_ice_eq
  {N : Nat}
  {c : Real}
  {x y h : SixVertexRow N}
-- given
  (hN : 0 < N)
  (hice : ¬svHorizontalIce hN x y h) :
-- imply
  svHorizontalRowWeight hN c x y h = 0 := by
-- proof
  apply StatMech.FrontierD.svHorizontalRowWeight_eq_zero_of_not_ice hN c hice

/--
[svHorizontalRowWeight_sum_formula](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedTransferBridge.lean)
-/
@[path]
private lemma svHorizontalRowWeight_sum_formula_eq
  {N : Nat}
  {c : Real}
  {x y : SixVertexRow N}
-- given
  (hN : 0 < N)
  (hcount : sixVertexUpCount x = sixVertexUpCount y) :
-- imply
  (∑ h : SixVertexRow N, svHorizontalRowWeight hN c x y h) = (if svRowPrefixForward x y then c ^ sixVertexRowDistance x y else 0) + (if svRowPrefixForward y x then c ^ sixVertexRowDistance x y else 0) := by
-- proof
  apply StatMech.FrontierD.svHorizontalRowWeight_sum_formula hN c x y hcount

/--
[svRowPrefixForward_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedTransferBridge.lean)
-/
@[path]
private lemma svRowPrefixForward_self_eq
  {N : Nat}
  {x : SixVertexRow N} :
-- imply
  svRowPrefixForward x x := by
-- proof
  apply StatMech.FrontierD.svRowPrefixForward_self x

/--
[svHorizontalRowWeight_sum_eq_transfer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedTransferBridge.lean)
-/
@[path]
private lemma svHorizontalRowWeight_sum_eq_transfer_eq
  {N : Nat}
  {c : Real}
  {x y : SixVertexRow N}
-- given
  (hN : 0 < N) :
-- imply
  (∑ h : SixVertexRow N, svHorizontalRowWeight hN c x y h) = sixVertexTransfer N c x y := by
-- proof
  apply StatMech.FrontierD.svHorizontalRowWeight_sum_eq_transfer hN c x y

/--
[svFinitePeriodicSucc_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedTransferBridge.lean)
-/
@[path]
private lemma svFinitePeriodicSucc_injective_eq
  {N : Nat}
-- given
  (hN : 0 < N) :
-- imply
  Function.Injective (finitePeriodicSucc hN) := by
-- proof
  apply StatMech.FrontierD.svFinitePeriodicSucc_injective hN

/--
[svFinitePeriodicSuccEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedTransferBridge.lean)
-/
@[path]
private lemma svFinitePeriodicSuccEquiv_apply_eq
  {N : Nat}
  {i : Fin N}
-- given
  (hN : 0 < N) :
-- imply
  svFinitePeriodicSuccEquiv hN i = finitePeriodicSucc hN i := by
-- proof
  apply StatMech.FrontierD.svFinitePeriodicSuccEquiv_apply hN i

/--
[svHorizontalLocalWeight_eq_torusLocalWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedTransferBridge.lean)
-/
@[path]
private lemma svHorizontalLocalWeight_eq_torusLocalWeight_eq
  {T : EvenTorus}
  {c : Real}
  {omega : SixVertexArrows T}
  {i : Fin T.width}
  {j : Fin T.height} :
-- imply
  svHorizontalLocalWeight T.width_pos c (svTorusVerticalRows T omega (SixVertexArrows.cyclicPred T.height_pos j)) (svTorusVerticalRows T omega j) (svTorusHorizontalRows T omega j) i = omega.localWeight c (i, j) := by
-- proof
  apply StatMech.FrontierD.svHorizontalLocalWeight_eq_torusLocalWeight T c omega i j

/--
[svTorusWeight_eq_product_rowWeights](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedTransferBridge.lean)
-/
@[path]
private lemma svTorusWeight_eq_product_rowWeights_eq
  {T : EvenTorus}
  {c : Real}
  {omega : SixVertexArrows T} :
-- imply
  omega.weight c = ∏ j : Fin T.height, svHorizontalRowWeight T.width_pos c (svTorusVerticalRows T omega (SixVertexArrows.cyclicPred T.height_pos j)) (svTorusVerticalRows T omega j) (svTorusHorizontalRows T omega j) := by
-- proof
  apply StatMech.FrontierD.svTorusWeight_eq_product_rowWeights T c omega

/--
[svTorusSeam_balanced_iff_lastRow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedTransferBridge.lean)
-/
@[path]
private lemma svTorusSeam_balanced_iff_lastRow_eq
  {T : EvenTorus}
  {omega : SixVertexArrows T} :
-- imply
  (sixVertexTorusSeam T omega).Balanced ↔ sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = T.width / 2 := by
-- proof
  apply StatMech.FrontierD.svTorusSeam_balanced_iff_lastRow T omega

/--
[svTorusBalancedArrowPartitionSum_eq_rowSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedTransferBridge.lean)
-/
@[path]
private lemma svTorusBalancedArrowPartitionSum_eq_rowSum_eq
  {T : EvenTorus}
  {c : Real} :
-- imply
  svTorusBalancedArrowPartitionSum T c = ∑ vrows : Fin T.height → SixVertexRow T.width, if sixVertexUpCount (vrows (svFinLast T.height_pos)) = T.width / 2 then ∏ j : Fin T.height, sixVertexTransfer T.width c (vrows (SixVertexArrows.cyclicPred T.height_pos j)) (vrows j) else 0 := by
-- proof
  apply StatMech.FrontierD.svTorusBalancedArrowPartitionSum_eq_rowSum T c

/--
[svCyclicPred_finitePeriodicSucc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedTransferBridge.lean)
-/
@[path]
private lemma svCyclicPred_finitePeriodicSucc_eq
  {N : Nat}
  {i : Fin N}
-- given
  (hN : 0 < N) :
-- imply
  SixVertexArrows.cyclicPred hN (finitePeriodicSucc hN i) = i := by
-- proof
  apply StatMech.FrontierD.svCyclicPred_finitePeriodicSucc hN i

/--
[svPredTransferProduct_eq_matrixCycleWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedTransferBridge.lean)
-/
@[path]
private lemma svPredTransferProduct_eq_matrixCycleWeight_eq
  {N M : Nat}
  {c : Real}
  {vrows : Fin M → SixVertexRow N}
-- given
  (hM : 0 < M) :
-- imply
  (∏ j : Fin M, sixVertexTransfer N c (vrows (SixVertexArrows.cyclicPred hM j)) (vrows j)) = matrixCycleWeight hM (sixVertexTransfer N c) vrows := by
-- proof
  apply StatMech.FrontierD.svPredTransferProduct_eq_matrixCycleWeight hM c vrows

/--
[svPeriodicRowsFixedSectorEquiv_weight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedTransferBridge.lean)
-/
@[path]
private lemma svPeriodicRowsFixedSectorEquiv_weight_eq
  {N M : Nat}
  {c : Real}
  {n : Fin (N + 1)}
  {x : SixVertexPeriodicRowsInSector N M hM c n}
-- given
  (hM : 0 < M) :
-- imply
  sixVertexPeriodicRowWeight hM c x.1 = matrixCycleWeight hM (sixVertexSectorTransfer N n c) (sixVertexPeriodicRowsFixedSectorEquiv N M hM c n x) := by
-- proof
  apply StatMech.FrontierD.svPeriodicRowsFixedSectorEquiv_weight N M hM c n x

/--
[svPeriodicRowsInSector_sum_eq_trace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedTransferBridge.lean)
-/
@[path]
private lemma svPeriodicRowsInSector_sum_eq_trace_eq
  {N M : Nat}
  {c : Real}
  {n : Fin (N + 1)}
-- given
  (hM : 0 < M) :
-- imply
  (∑ x : SixVertexPeriodicRowsInSector N M hM c n, sixVertexPeriodicRowWeight hM c x.1) = Matrix.trace (sixVertexSectorTransfer N n c ^ M) := by
-- proof
  apply StatMech.FrontierD.svPeriodicRowsInSector_sum_eq_trace N M hM c n

/--
[svTorusBalancedArrowPartitionSum_eq_sectorTrace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedTransferBridge.lean)
-/
@[path]
private lemma svTorusBalancedArrowPartitionSum_eq_sectorTrace_eq
  {T : EvenTorus}
  {c : Real} :
-- imply
  svTorusBalancedArrowPartitionSum T c = Matrix.trace (sixVertexSectorTransfer T.width (T.width / 2) c ^ T.height) := by
-- proof
  apply StatMech.FrontierD.svTorusBalancedArrowPartitionSum_eq_sectorTrace T c

/--
[sixVertexRectangleBalancedPartitionSum_eq_torusBalancedArrow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedTransferBridge.lean)
-/
@[path]
private lemma sixVertexRectangleBalancedPartitionSum_eq_torusBalancedArrow_eq
  {T : EvenTorus}
  {c : Real} :
-- imply
  sixVertexRectangleBalancedPartitionSum T.width T.height c = svTorusBalancedArrowPartitionSum T c := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleBalancedPartitionSum_eq_torusBalancedArrow T c

/--
[sixVertexRectangleBalancedPartitionSum_eq_halfFilledTrace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedTransferBridge.lean)
-/
@[path]
private lemma sixVertexRectangleBalancedPartitionSum_eq_halfFilledTrace_eq
  {T : EvenTorus}
  {c : Real} :
-- imply
  sixVertexRectangleBalancedPartitionSum T.width T.height c = Matrix.trace (sixVertexSectorTransfer T.width (T.width / 2) c ^ T.height) := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleBalancedPartitionSum_eq_halfFilledTrace T c


-- created on 2026-10-23
