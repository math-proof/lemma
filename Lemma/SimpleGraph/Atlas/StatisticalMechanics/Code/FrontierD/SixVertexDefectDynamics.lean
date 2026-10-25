import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDefectDynamics.Part7
open Finset StatMech StatMech.FrontierD


/--
[sixVertexDefectLower_apply_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDefectDynamics.lean)
-/
@[path]
private lemma sixVertexDefectLower_apply_self_eq
  {n : Nat}
  {d : Fin n → Nat}
  {i : Fin n}
-- given
  (hi : 0 < i.val) :
-- imply
  sixVertexDefectLower d i hi i = d i - 1 := by
-- proof
  apply StatMech.FrontierD.sixVertexDefectLower_apply_self d i hi

/--
[sixVertexDefectLower_apply_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDefectDynamics.lean)
-/
@[path]
private lemma sixVertexDefectLower_apply_pred_eq
  {n : Nat}
  {d : Fin n → Nat}
  {i : Fin n}
-- given
  (hi : 0 < i.val) :
-- imply
  sixVertexDefectLower d i hi ⟨i.val - 1, by omega⟩ = d ⟨i.val - 1, by omega⟩ + 1 := by
-- proof
  apply StatMech.FrontierD.sixVertexDefectLower_apply_pred d i hi

/--
[sum_sixVertexDefectLower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDefectDynamics.lean)
-/
@[path]
private lemma sum_sixVertexDefectLower_eq
  {n : Nat}
  {d : Fin n → Nat}
  {i : Fin n}
-- given
  (hi : 0 < i.val)
  (hd : 0 < d i) :
-- imply
  ∑ j, sixVertexDefectLower d i hi j = ∑ j, d j := by
-- proof
  apply StatMech.FrontierD.sum_sixVertexDefectLower d i hi hd

/--
[sixVertexDefectWeight_lower_add_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDefectDynamics.lean)
-/
@[path]
private lemma sixVertexDefectWeight_lower_add_one_eq
  {n : Nat}
  {d : Fin n → Nat}
  {i : Fin n}
-- given
  (hi : 0 < i.val)
  (hd : 0 < d i) :
-- imply
  sixVertexDefectWeight (sixVertexDefectLower d i hi) + 1 = sixVertexDefectWeight d := by
-- proof
  apply StatMech.FrontierD.sixVertexDefectWeight_lower_add_one d i hi hd

/--
[sixVertexDefectWeight_eq_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDefectDynamics.lean)
-/
@[path]
private lemma sixVertexDefectWeight_eq_zero_iff_eq
  {n : Nat}
  {d : Fin n → Nat} :
-- imply
  sixVertexDefectWeight d = 0 ↔ ∀ i, 0 < i.val → d i = 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexDefectWeight_eq_zero_iff d

/--
[sixVertexDefectPile_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDefectDynamics.lean)
-/
@[path]
private lemma sixVertexDefectPile_sum_eq
  {n : Nat}
  {D : Nat}
-- given
  (hn : 0 < n) :
-- imply
  ∑ i, sixVertexDefectPile hn D i = D := by
-- proof
  apply StatMech.FrontierD.sixVertexDefectPile_sum hn D

/--
[sixVertexDefect_eq_pile_of_weight_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDefectDynamics.lean)
-/
@[path]
private lemma sixVertexDefect_eq_pile_of_weight_eq_zero_eq
  {n : Nat}
  {d : Fin n → Nat}
-- given
  (hn : 0 < n)
  (hweight : sixVertexDefectWeight d = 0) :
-- imply
  d = sixVertexDefectPile hn (∑ i, d i) := by
-- proof
  apply StatMech.FrontierD.sixVertexDefect_eq_pile_of_weight_eq_zero hn d hweight

/--
[sixVertexDefectLowerStep_reaches_pile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDefectDynamics.lean)
-/
@[path]
private lemma sixVertexDefectLowerStep_reaches_pile_eq
  {n : Nat}
  {d : Fin n → Nat}
-- given
  (hn : 0 < n) :
-- imply
  Relation.ReflTransGen SixVertexDefectLowerStep d (sixVertexDefectPile hn (∑ i, d i)) := by
-- proof
  apply StatMech.FrontierD.sixVertexDefectLowerStep_reaches_pile hn d

/--
[SixVertexDefectLowerStep.sum_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDefectDynamics.lean)
-/
@[path]
private lemma sum_eq_eq
  {n : Nat}
  {d e : Fin n → Nat}
-- given
  (h : SixVertexDefectLowerStep d e) :
-- imply
  ∑ i, e i = ∑ i, d i := by
-- proof
  apply StatMech.FrontierD.SixVertexDefectLowerStep.sum_eq h

/--
[SixVertexDefectLowerStep.weight_add_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDefectDynamics.lean)
-/
@[path]
private lemma weight_add_one_eq
  {n : Nat}
  {d e : Fin n → Nat}
-- given
  (h : SixVertexDefectLowerStep d e) :
-- imply
  sixVertexDefectWeight e + 1 = sixVertexDefectWeight d := by
-- proof
  apply StatMech.FrontierD.SixVertexDefectLowerStep.weight_add_one h

/--
[sixVertexDefectLowerGraph_reachable_pile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDefectDynamics.lean)
-/
@[path]
private lemma sixVertexDefectLowerGraph_reachable_pile_eq
  {n D : Nat}
  {d : SixVertexDefectState n D}
-- given
  (hn : 0 < n) :
-- imply
  (sixVertexDefectLowerGraph n D).Reachable d ⟨sixVertexDefectPile hn D, sixVertexDefectPile_sum hn D⟩ := by
-- proof
  apply StatMech.FrontierD.sixVertexDefectLowerGraph_reachable_pile hn d

/--
[sixVertexDefectLowerGraph_preconnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDefectDynamics.lean)
-/
@[path]
private lemma sixVertexDefectLowerGraph_preconnected_eq
  {n D : Nat}
-- given
  (hn : 0 < n) :
-- imply
  (sixVertexDefectLowerGraph n D).Preconnected := by
-- proof
  apply StatMech.FrontierD.sixVertexDefectLowerGraph_preconnected hn

/--
[sixVertexFixedChargeSectorDefectState_reachable_pile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDefectDynamics.lean)
-/
@[path]
private lemma sixVertexFixedChargeSectorDefectState_reachable_pile_eq
  {r k : Nat}
  {x : SixVertexSector (sixVertexFourWidth r k) (sixVertexFixedChargeBetheParticleCount r k)}
-- given
  (hx : SixVertexSectorNoAdjacent x) :
-- imply
  (sixVertexDefectLowerGraph (sixVertexFixedChargeBetheParticleCount r k) (2 * r)).Reachable (sixVertexFixedChargeSectorDefectState r k x hx) ⟨sixVertexDefectPile (sixVertexFixedChargeBetheParticleCount_pos r k) (2 * r), sixVertexDefectPile_sum (sixVertexFixedChargeBetheParticleCount_pos r k) (2 * r)⟩ := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedChargeSectorDefectState_reachable_pile r k x hx

/--
[sixVertexSectorPosition_forwardMoveSector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDefectDynamics.lean)
-/
@[path]
private lemma sixVertexSectorPosition_forwardMoveSector_eq
  {N n : Nat}
  {x : SixVertexSector N n}
  {a : Fin n → Nat}
-- given
  (hbound : ∀ i, (sixVertexSectorPosition x i).val + a i < N)
  (hmono : ∀ i j : Fin n, i < j → (sixVertexSectorPosition x i).val + a i < (sixVertexSectorPosition x j).val + a j) :
-- imply
  sixVertexSectorPosition (sixVertexForwardMoveSector x a hbound hmono) = sixVertexForwardMoveEmbedding x a hbound hmono := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorPosition_forwardMoveSector x a hbound hmono

/--
[sixVertexSectorPosition_forwardMoveSector_apply_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDefectDynamics.lean)
-/
@[path]
private lemma sixVertexSectorPosition_forwardMoveSector_apply_val_eq
  {N n : Nat}
  {x : SixVertexSector N n}
  {a : Fin n → Nat}
  {i : Fin n}
-- given
  (hbound : ∀ i, (sixVertexSectorPosition x i).val + a i < N)
  (hmono : ∀ i j : Fin n, i < j → (sixVertexSectorPosition x i).val + a i < (sixVertexSectorPosition x j).val + a j) :
-- imply
  (sixVertexSectorPosition (sixVertexForwardMoveSector x a hbound hmono) i).val = (sixVertexSectorPosition x i).val + a i := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorPosition_forwardMoveSector_apply_val x a hbound hmono i

/--
[sixVertexInfinityGraph_adj_forwardMoveSector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDefectDynamics.lean)
-/
@[path]
private lemma sixVertexInfinityGraph_adj_forwardMoveSector_eq
  {N n : Nat}
  {x : SixVertexSector N n}
  {a : Fin n → Nat}
-- given
  (hn : 0 < n)
  (hbound : ∀ i, (sixVertexSectorPosition x i).val + a i < N)
  (hmono : ∀ i j : Fin n, i < j → (sixVertexSectorPosition x i).val + a i < (sixVertexSectorPosition x j).val + a j)
  (hpos : ∀ i, 0 < a i)
  (hbetween : ∀ (k : Nat) (hk : k + 1 < n), (sixVertexSectorPosition x ⟨k, by omega⟩).val + a ⟨k, by omega⟩ < (sixVertexSectorPosition x ⟨k + 1, hk⟩).val) :
-- imply
  (sixVertexInfinityGraph N n).Adj x (sixVertexForwardMoveSector x a hbound hmono) := by
-- proof
  apply StatMech.FrontierD.sixVertexInfinityGraph_adj_forwardMoveSector hn x a hbound hmono hpos hbetween

/--
[sixVertexSectorCyclicNext_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDefectDynamics.lean)
-/
@[path]
private lemma sixVertexSectorCyclicNext_pred_eq
  {n : Nat}
  {i : Fin n}
-- given
  (hi : 0 < i.val) :
-- imply
  sixVertexSectorCyclicNext ⟨i.val - 1, by omega⟩ = i := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorCyclicNext_pred i hi

/--
[sixVertexSectorCyclicNext_eq_iff_eq_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDefectDynamics.lean)
-/
@[path]
private lemma sixVertexSectorCyclicNext_eq_iff_eq_pred_eq
  {n : Nat}
  {i j : Fin n}
-- given
  (hi : 0 < i.val) :
-- imply
  sixVertexSectorCyclicNext j = i ↔ j = ⟨i.val - 1, by omega⟩ := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorCyclicNext_eq_iff_eq_pred i j hi

/--
[sixVertexDefectLowerAdvance_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDefectDynamics.lean)
-/
@[path]
private lemma sixVertexDefectLowerAdvance_pos_eq
  {n : Nat}
  {i j : Fin n} :
-- imply
  0 < sixVertexDefectLowerAdvance i j := by
-- proof
  apply StatMech.FrontierD.sixVertexDefectLowerAdvance_pos i j

/--
[sixVertexDefectLowerAdvance_sub_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDefectDynamics.lean)
-/
@[path]
private lemma sixVertexDefectLowerAdvance_sub_one_eq
  {n : Nat}
  {i j : Fin n} :
-- imply
  sixVertexDefectLowerAdvance i j - 1 = if j = i then 1 else 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexDefectLowerAdvance_sub_one i j

/--
[sixVertexDefectLowerMove_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDefectDynamics.lean)
-/
@[path]
private lemma sixVertexDefectLowerMove_bound_eq
  {N n : Nat}
  {x : SixVertexSector N n}
  {i : Fin n}
-- given
  (hx : SixVertexSectorNoAdjacent x)
  (hn : 0 < n)
  (hd : 0 < sixVertexSectorGapDefects x i)
  (hlast : (sixVertexSectorPosition x ⟨n - 1, by omega⟩).val + sixVertexDefectLowerAdvance i ⟨n - 1, by omega⟩ < N) :
-- imply
  ∀ j, (sixVertexSectorPosition x j).val + sixVertexDefectLowerAdvance i j < N := by
-- proof
  apply StatMech.FrontierD.sixVertexDefectLowerMove_bound x hx hn i hd hlast

/--
[sixVertexDefectLowerMove_between](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDefectDynamics.lean)
-/
@[path]
private lemma sixVertexDefectLowerMove_between_eq
  {N n : Nat}
  {x : SixVertexSector N n}
  {i : Fin n}
  {k : Nat}
-- given
  (hx : SixVertexSectorNoAdjacent x)
  (hd : 0 < sixVertexSectorGapDefects x i)
  (hk : k + 1 < n) :
-- imply
  (sixVertexSectorPosition x ⟨k, by omega⟩).val + sixVertexDefectLowerAdvance i ⟨k, by omega⟩ < (sixVertexSectorPosition x ⟨k + 1, hk⟩).val := by
-- proof
  apply StatMech.FrontierD.sixVertexDefectLowerMove_between x hx i hd k hk

/--
[sixVertexDefectLowerMove_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDefectDynamics.lean)
-/
@[path]
private lemma sixVertexDefectLowerMove_mono_eq
  {N n : Nat}
  {x : SixVertexSector N n}
  {i : Fin n}
-- given
  (hx : SixVertexSectorNoAdjacent x)
  (hd : 0 < sixVertexSectorGapDefects x i) :
-- imply
  ∀ j k : Fin n, j < k → (sixVertexSectorPosition x j).val + sixVertexDefectLowerAdvance i j < (sixVertexSectorPosition x k).val + sixVertexDefectLowerAdvance i k := by
-- proof
  apply StatMech.FrontierD.sixVertexDefectLowerMove_mono x hx i hd

/--
[sixVertexSectorPosition_defectLowerMoveSector_apply_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDefectDynamics.lean)
-/
@[path]
private lemma sixVertexSectorPosition_defectLowerMoveSector_apply_val_eq
  {N n : Nat}
  {x : SixVertexSector N n}
  {i : Fin n}
  {j : Fin n}
-- given
  (hx : SixVertexSectorNoAdjacent x)
  (hn : 0 < n)
  (hd : 0 < sixVertexSectorGapDefects x i)
  (hlast : (sixVertexSectorPosition x ⟨n - 1, by omega⟩).val + sixVertexDefectLowerAdvance i ⟨n - 1, by omega⟩ < N) :
-- imply
  (sixVertexSectorPosition (sixVertexDefectLowerMoveSector x hx hn i hd hlast) j).val = (sixVertexSectorPosition x j).val + sixVertexDefectLowerAdvance i j := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorPosition_defectLowerMoveSector_apply_val x hx hn i hd hlast j

/--
[sixVertexInfinityGraph_adj_defectLowerMove_of_last_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDefectDynamics.lean)
-/
@[path]
private lemma sixVertexInfinityGraph_adj_defectLowerMove_of_last_bound_eq
  {N n : Nat}
  {x : SixVertexSector N n}
  {i : Fin n}
-- given
  (hx : SixVertexSectorNoAdjacent x)
  (hn : 0 < n)
  (hi : 0 < i.val)
  (hd : 0 < sixVertexSectorGapDefects x i)
  (hlast : (sixVertexSectorPosition x ⟨n - 1, by omega⟩).val + sixVertexDefectLowerAdvance i ⟨n - 1, by omega⟩ < N) :
-- imply
  (sixVertexInfinityGraph N n).Adj x (sixVertexDefectLowerMoveSector x hx hn i hd hlast) := by
-- proof
  apply StatMech.FrontierD.sixVertexInfinityGraph_adj_defectLowerMove_of_last_bound x hx hn i hi hd hlast

/--
[sixVertexDefectLowerMoveSector_gapDefects](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDefectDynamics.lean)
-/
@[path]
private lemma sixVertexDefectLowerMoveSector_gapDefects_eq
  {N n : Nat}
  {x : SixVertexSector N n}
  {i : Fin n}
-- given
  (hx : SixVertexSectorNoAdjacent x)
  (hn : 0 < n)
  (hi : 0 < i.val)
  (hd : 0 < sixVertexSectorGapDefects x i)
  (hlast : (sixVertexSectorPosition x ⟨n - 1, by omega⟩).val + sixVertexDefectLowerAdvance i ⟨n - 1, by omega⟩ < N) :
-- imply
  sixVertexSectorGapDefects (sixVertexDefectLowerMoveSector x hx hn i hd hlast) = sixVertexDefectLower (sixVertexSectorGapDefects x) i hi := by
-- proof
  apply StatMech.FrontierD.sixVertexDefectLowerMoveSector_gapDefects x hx hn i hi hd hlast

/--
[sixVertexSectorPosition_shiftLeftSector_apply_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDefectDynamics.lean)
-/
@[path]
private lemma sixVertexSectorPosition_shiftLeftSector_apply_val_eq
  {N n : Nat}
  {x : SixVertexSector N n}
  {i : Fin n}
-- given
  (hn : 0 < n)
  (hfirst : 0 < (sixVertexSectorPosition x ⟨0, hn⟩).val) :
-- imply
  (sixVertexSectorPosition (sixVertexShiftLeftSector x hn hfirst) i).val = (sixVertexSectorPosition x i).val - 1 := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorPosition_shiftLeftSector_apply_val x hn hfirst i

/--
[sixVertexShiftLeftSector_noAdjacent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDefectDynamics.lean)
-/
@[path]
private lemma sixVertexShiftLeftSector_noAdjacent_eq
  {N n : Nat}
  {x : SixVertexSector N n}
-- given
  (hx : SixVertexSectorNoAdjacent x)
  (hn : 0 < n)
  (hfirst : 0 < (sixVertexSectorPosition x ⟨0, hn⟩).val) :
-- imply
  SixVertexSectorNoAdjacent (sixVertexShiftLeftSector x hn hfirst) := by
-- proof
  apply StatMech.FrontierD.sixVertexShiftLeftSector_noAdjacent x hx hn hfirst

/--
[sixVertexShiftLeftSector_gapDefects](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDefectDynamics.lean)
-/
@[path]
private lemma sixVertexShiftLeftSector_gapDefects_eq
  {N n : Nat}
  {x : SixVertexSector N n}
-- given
  (hn : 0 < n)
  (hfirst : 0 < (sixVertexSectorPosition x ⟨0, hn⟩).val) :
-- imply
  sixVertexSectorGapDefects (sixVertexShiftLeftSector x hn hfirst) = sixVertexSectorGapDefects x := by
-- proof
  apply StatMech.FrontierD.sixVertexShiftLeftSector_gapDefects x hn hfirst

/--
[sixVertexInfinityGraph_adj_shiftLeftSector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDefectDynamics.lean)
-/
@[path]
private lemma sixVertexInfinityGraph_adj_shiftLeftSector_eq
  {N n : Nat}
  {x : SixVertexSector N n}
-- given
  (hx : SixVertexSectorNoAdjacent x)
  (hn : 0 < n)
  (hfirst : 0 < (sixVertexSectorPosition x ⟨0, hn⟩).val) :
-- imply
  (sixVertexInfinityGraph N n).Adj x (sixVertexShiftLeftSector x hn hfirst) := by
-- proof
  apply StatMech.FrontierD.sixVertexInfinityGraph_adj_shiftLeftSector x hx hn hfirst

/--
[sixVertexDefectLowerMove_first_pos_of_not_last_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDefectDynamics.lean)
-/
@[path]
private lemma sixVertexDefectLowerMove_first_pos_of_not_last_bound_eq
  {N n : Nat}
  {x : SixVertexSector N n}
  {i : Fin n}
-- given
  (hx : SixVertexSectorNoAdjacent x)
  (hn : 0 < n)
  (hd : 0 < sixVertexSectorGapDefects x i)
  (hbound : ¬((sixVertexSectorPosition x ⟨n - 1, by omega⟩).val + sixVertexDefectLowerAdvance i ⟨n - 1, by omega⟩ < N)) :
-- imply
  0 < (sixVertexSectorPosition x ⟨0, hn⟩).val := by
-- proof
  apply StatMech.FrontierD.sixVertexDefectLowerMove_first_pos_of_not_last_bound x hx hn i hd hbound

/--
[sixVertexInfinityGraph_reachable_defectLower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDefectDynamics.lean)
-/
@[path]
private lemma sixVertexInfinityGraph_reachable_defectLower_eq
  {N n : Nat}
  {x : SixVertexSector N n}
  {i : Fin n}
-- given
  (hx : SixVertexSectorNoAdjacent x)
  (hn : 0 < n)
  (hi : 0 < i.val)
  (hd : 0 < sixVertexSectorGapDefects x i) :
-- imply
  ∃ y : SixVertexSector N n, SixVertexSectorNoAdjacent y ∧ (sixVertexInfinityGraph N n).Reachable x y ∧ sixVertexSectorGapDefects y = sixVertexDefectLower (sixVertexSectorGapDefects x) i hi := by
-- proof
  apply StatMech.FrontierD.sixVertexInfinityGraph_reachable_defectLower x hx hn i hi hd

/--
[sixVertexInfinityGraph_reachable_of_defectLowerSteps](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDefectDynamics.lean)
-/
@[path]
private lemma sixVertexInfinityGraph_reachable_of_defectLowerSteps_eq
  {N n : Nat}
  {x : SixVertexSector N n}
  {d : Fin n → Nat}
-- given
  (hn : 0 < n)
  (hx : SixVertexSectorNoAdjacent x)
  (hsteps : Relation.ReflTransGen SixVertexDefectLowerStep (sixVertexSectorGapDefects x) d) :
-- imply
  ∃ y : SixVertexSector N n, SixVertexSectorNoAdjacent y ∧ (sixVertexInfinityGraph N n).Reachable x y ∧ sixVertexSectorGapDefects y = d := by
-- proof
  apply StatMech.FrontierD.sixVertexInfinityGraph_reachable_of_defectLowerSteps hn x hx hsteps

/--
[sixVertexInfinityGraph_reachable_first_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDefectDynamics.lean)
-/
@[path]
private lemma sixVertexInfinityGraph_reachable_first_zero_eq
  {N n : Nat}
  {x : SixVertexSector N n}
-- given
  (hn : 0 < n)
  (hx : SixVertexSectorNoAdjacent x) :
-- imply
  ∃ y : SixVertexSector N n, SixVertexSectorNoAdjacent y ∧ (sixVertexInfinityGraph N n).Reachable x y ∧ sixVertexSectorGapDefects y = sixVertexSectorGapDefects x ∧ (sixVertexSectorPosition y ⟨0, hn⟩).val = 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexInfinityGraph_reachable_first_zero hn x hx

/--
[sixVertexSector_eq_of_gapDefects_eq_of_first_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDefectDynamics.lean)
-/
@[path]
private lemma sixVertexSector_eq_of_gapDefects_eq_of_first_eq_eq
  {N n : Nat}
  {x y : SixVertexSector N n}
-- given
  (hn : 0 < n)
  (hx : SixVertexSectorNoAdjacent x)
  (hy : SixVertexSectorNoAdjacent y)
  (hgap : sixVertexSectorGapDefects x = sixVertexSectorGapDefects y)
  (hfirst : (sixVertexSectorPosition x ⟨0, hn⟩).val = (sixVertexSectorPosition y ⟨0, hn⟩).val) :
-- imply
  x = y := by
-- proof
  apply StatMech.FrontierD.sixVertexSector_eq_of_gapDefects_eq_of_first_eq hn x y hx hy hgap hfirst

/--
[sixVertexNoAdjacentInfinityGraph_reachable_of_full](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDefectDynamics.lean)
-/
@[path]
private lemma sixVertexNoAdjacentInfinityGraph_reachable_of_full_eq
  {N n : Nat}
  {x y : SixVertexNoAdjacentSector N n}
-- given
  (h : (sixVertexInfinityGraph N n).Reachable x.1 y.1) :
-- imply
  (sixVertexNoAdjacentInfinityGraph N n).Reachable x y := by
-- proof
  apply StatMech.FrontierD.sixVertexNoAdjacentInfinityGraph_reachable_of_full x y h

/--
[sixVertexNoAdjacentInfinityGraph_preconnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDefectDynamics.lean)
-/
@[path]
private lemma sixVertexNoAdjacentInfinityGraph_preconnected_eq
  {N n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  (sixVertexNoAdjacentInfinityGraph N n).Preconnected := by
-- proof
  apply StatMech.FrontierD.sixVertexNoAdjacentInfinityGraph_preconnected hn

/--
[sixVertexNoAdjacentTransferInfinity_pow_apply_eq_card_walk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDefectDynamics.lean)
-/
@[path]
private lemma sixVertexNoAdjacentTransferInfinity_pow_apply_eq_card_walk_eq
  {M N n : Nat}
  {x y : SixVertexNoAdjacentSector N n} :
-- imply
  (sixVertexNoAdjacentTransferInfinity N n ^ M) x y = Fintype.card {w : (sixVertexNoAdjacentInfinityGraph N n).Walk x y | w.length = M} := by
-- proof
  apply StatMech.FrontierD.sixVertexNoAdjacentTransferInfinity_pow_apply_eq_card_walk M N n x y

/--
[sixVertexNoAdjacentTransferInfinity_isIrreducible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDefectDynamics.lean)
-/
@[path]
private lemma sixVertexNoAdjacentTransferInfinity_isIrreducible_eq
  {N n : Nat}
-- given
  (hn : 0 < n)
  (hhalf : 2 * n ≤ N) :
-- imply
  (sixVertexNoAdjacentTransferInfinity N n).IsIrreducible := by
-- proof
  apply StatMech.FrontierD.sixVertexNoAdjacentTransferInfinity_isIrreducible hn hhalf


-- created on 2026-10-23
