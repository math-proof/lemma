import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectMedialLoopTurnClassification
open Equiv Finset StatMech StatMech.FrontierD


/--
[fkMedialBlackBoundaryPerm_iterate_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialLoopTurnClassification.lean)
-/
@[path]
private lemma fkMedialBlackBoundaryPerm_iterate_val_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {d : FKMedialBlackDart T}
  {n : Nat} :
-- imply
  (((fkMedialBlackBoundaryPerm pairing)^[n] d).1) = (fkMedialBoundaryStep pairing)^[n] d.1 := by
-- proof
  apply StatMech.FrontierD.fkMedialBlackBoundaryPerm_iterate_val pairing d n

/--
[fkRectRefinedBoundaryCenterAfter_succ_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialLoopTurnClassification.lean)
-/
@[path]
private lemma fkRectRefinedBoundaryCenterAfter_succ_right_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {d : FKMedialDart T}
  {c : Int × Int}
  {n : Nat} :
-- imply
  fkRectRefinedBoundaryCenterAfter pairing d c (n + 1) = fkRectRefinedBondCenter (fkRectRefinedBoundaryCenterAfter pairing d c n) (fkMedialLocalMate pairing ((fkMedialBoundaryStep pairing)^[n] d)).2 := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedBoundaryCenterAfter_succ_right pairing d c n

/--
[fkRectBlackBoundaryPointAfter_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialLoopTurnClassification.lean)
-/
@[path]
private lemma fkRectBlackBoundaryPointAfter_succ_eq
  {T : EvenTorus}
  {R : FKRectTorus}
  {pairing : FKMedialLoopPairing R.medialTorus}
  {d : FKMedialBlackDart R.medialTorus}
  {n : Nat} :
-- imply
  fkRectBlackBoundaryPointAfter R pairing d (n + 1) = ((fkRectBlackBoundaryPointAfter R pairing d n).1 + 2 * ons_dirExponentX (fkMedialStrandDirection pairing ((fkMedialBlackBoundaryPerm pairing)^[n] d).1), (fkRectBlackBoundaryPointAfter R pairing d n).2 + 2 * ons_dirExponentY (fkMedialStrandDirection pairing ((fkMedialBlackBoundaryPerm pairing)^[n] d).1)) := by
-- proof
  apply StatMech.FrontierD.fkRectBlackBoundaryPointAfter_succ R pairing d n

/--
[fkRectBlackOrbitList_mem_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialLoopTurnClassification.lean)
-/
@[path]
private lemma fkRectBlackOrbitList_mem_self_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {d : FKMedialBlackDart T} :
-- imply
  d ∈ fkRectBlackOrbitList pairing d := by
-- proof
  apply StatMech.FrontierD.fkRectBlackOrbitList_mem_self pairing d

/--
[fkRectBlackOrbitList_length_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialLoopTurnClassification.lean)
-/
@[path]
private lemma fkRectBlackOrbitList_length_pos_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {d : FKMedialBlackDart T} :
-- imply
  0 < (fkRectBlackOrbitList pairing d).length := by
-- proof
  apply StatMech.FrontierD.fkRectBlackOrbitList_length_pos pairing d

/--
[fkRectBlackOrbitList_get](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialLoopTurnClassification.lean)
-/
@[path]
private lemma fkRectBlackOrbitList_get_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {d : FKMedialBlackDart T}
  {i : Fin (fkRectBlackOrbitList pairing d).length} :
-- imply
  (fkRectBlackOrbitList pairing d).get i = (fkMedialBlackBoundaryPerm pairing)^[i.val] d := by
-- proof
  apply StatMech.FrontierD.fkRectBlackOrbitList_get pairing d i

/--
[fkRectBlackOrbitPrefix_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialLoopTurnClassification.lean)
-/
@[path]
private lemma fkRectBlackOrbitPrefix_zero_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {d : FKMedialBlackDart T} :
-- imply
  fkRectBlackOrbitPrefix pairing d 0 = 0 := by
-- proof
  apply StatMech.FrontierD.fkRectBlackOrbitPrefix_zero pairing d

/--
[fkRectBlackOrbitPrefix_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialLoopTurnClassification.lean)
-/
@[path]
private lemma fkRectBlackOrbitPrefix_succ_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {d : FKMedialBlackDart T}
  {n : Nat} :
-- imply
  fkRectBlackOrbitPrefix pairing d (n + 1) = fkRectBlackOrbitPrefix pairing d n + stepOf (fkMedialStrandDirection pairing ((fkMedialBlackBoundaryPerm pairing)^[n] d).1) := by
-- proof
  apply StatMech.FrontierD.fkRectBlackOrbitPrefix_succ pairing d n

/--
[fkRectBlackBoundaryPointAfter_eq_prefix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialLoopTurnClassification.lean)
-/
@[path]
private lemma fkRectBlackBoundaryPointAfter_eq_prefix_eq
  {T : EvenTorus}
  {R : FKRectTorus}
  {pairing : FKMedialLoopPairing R.medialTorus}
  {d : FKMedialBlackDart R.medialTorus}
  {n : Nat} :
-- imply
  fkRectBlackBoundaryPointAfter R pairing d n = fkRectBlackBoundaryPointAfter R pairing d 0 + 2 • fkRectBlackOrbitPrefix pairing d n := by
-- proof
  apply StatMech.FrontierD.fkRectBlackBoundaryPointAfter_eq_prefix R pairing d n

/--
[fkRectBlackOrbitPrefix_eq_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialLoopTurnClassification.lean)
-/
@[path]
private lemma fkRectBlackOrbitPrefix_eq_pos_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {d : FKMedialBlackDart T}
  [NeZero (fkRectBlackOrbitList pairing d).length]
  {i : Fin (fkRectBlackOrbitList pairing d).length} :
-- imply
  fkRectBlackOrbitPrefix pairing d i.val = pos (fkRectBlackOrbitDirection pairing d) i := by
-- proof
  apply StatMech.FrontierD.fkRectBlackOrbitPrefix_eq_pos pairing d i

/--
[fkRectBlackOrbitPrefix_length_eq_displacement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialLoopTurnClassification.lean)
-/
@[path]
private lemma fkRectBlackOrbitPrefix_length_eq_displacement_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {d : FKMedialBlackDart T} :
-- imply
  fkRectBlackOrbitPrefix pairing d (fkRectBlackOrbitList pairing d).length = ons_pathDisplacement (List.ofFn (fkRectBlackOrbitDirection pairing d)) := by
-- proof
  apply StatMech.FrontierD.fkRectBlackOrbitPrefix_length_eq_displacement pairing d

/--
[fkRectBlackBoundaryPerm_pow_length_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialLoopTurnClassification.lean)
-/
@[path]
private lemma fkRectBlackBoundaryPerm_pow_length_apply_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {d : FKMedialBlackDart T} :
-- imply
  (fkMedialBlackBoundaryPerm pairing)^[ (fkRectBlackOrbitList pairing d).length] d = d := by
-- proof
  apply StatMech.FrontierD.fkRectBlackBoundaryPerm_pow_length_apply pairing d

/--
[fkRectBlackBoundaryPointAfter_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialLoopTurnClassification.lean)
-/
@[path]
private lemma fkRectBlackBoundaryPointAfter_zero_eq
  {T : EvenTorus}
  {R : FKRectTorus}
  {pairing : FKMedialLoopPairing R.medialTorus}
  {d : FKMedialBlackDart R.medialTorus} :
-- imply
  fkRectBlackBoundaryPointAfter R pairing d 0 = fkRectBlackDartShiftedPoint R (0, 0) d := by
-- proof
  apply StatMech.FrontierD.fkRectBlackBoundaryPointAfter_zero R pairing d

/--
[fkRectBlackDeckPointShift_nsmul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialLoopTurnClassification.lean)
-/
@[path]
private lemma fkRectBlackDeckPointShift_nsmul_eq
  {T : EvenTorus}
  {R : FKRectTorus}
  {r : Nat}
  {u : Int × Int} :
-- imply
  fkRectBlackDeckPointShift R (r • u) = r • fkRectBlackDeckPointShift R u := by
-- proof
  apply StatMech.FrontierD.fkRectBlackDeckPointShift_nsmul R r u

/--
[fkRectBlackDartShiftedPoint_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialLoopTurnClassification.lean)
-/
@[path]
private lemma fkRectBlackDartShiftedPoint_add_eq
  {T : EvenTorus}
  {R : FKRectTorus}
  {u v : Int × Int}
  {d : FKMedialBlackDart R.medialTorus} :
-- imply
  fkRectBlackDartShiftedPoint R (u + v) d = fkRectBlackDartShiftedPoint R u d + fkRectBlackDeckPointShift R v := by
-- proof
  apply StatMech.FrontierD.fkRectBlackDartShiftedPoint_add R u v d

/--
[fkRectBlackBoundaryPointAfter_exists_shiftedPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialLoopTurnClassification.lean)
-/
@[path]
private lemma fkRectBlackBoundaryPointAfter_exists_shiftedPoint_eq
  {T : EvenTorus}
  {R : FKRectTorus}
  {pairing : FKMedialLoopPairing R.medialTorus}
  {d : FKMedialBlackDart R.medialTorus}
  {n : Nat} :
-- imply
  ∃ u : Int × Int, fkRectBlackBoundaryPointAfter R pairing d n = fkRectBlackDartShiftedPoint R u ((fkMedialBlackBoundaryPerm pairing)^[n] d) := by
-- proof
  apply StatMech.FrontierD.fkRectBlackBoundaryPointAfter_exists_shiftedPoint R pairing d n

/--
[fkRectBlackOrbit_pos_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialLoopTurnClassification.lean)
-/
@[path]
private lemma fkRectBlackOrbit_pos_injective_eq
  {T : EvenTorus}
  {R : FKRectTorus}
  {pairing : FKMedialLoopPairing R.medialTorus}
  {d : FKMedialBlackDart R.medialTorus}
  [NeZero (fkRectBlackOrbitList pairing d).length] :
-- imply
  Function.Injective (pos (fkRectBlackOrbitDirection pairing d)) := by
-- proof
  apply StatMech.FrontierD.fkRectBlackOrbit_pos_injective R pairing d

/--
[fkMedialStrandDirection_blackBoundaryPerm_ne_add_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialLoopTurnClassification.lean)
-/
@[path]
private lemma fkMedialStrandDirection_blackBoundaryPerm_ne_add_two_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {d : FKMedialBlackDart T} :
-- imply
  fkMedialStrandDirection pairing (fkMedialBlackBoundaryPerm pairing d).1 ≠ fkMedialStrandDirection pairing d.1 + 2 := by
-- proof
  apply StatMech.FrontierD.fkMedialStrandDirection_blackBoundaryPerm_ne_add_two pairing d

/--
[fkRectBlackOrbitDirection_nonUturn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialLoopTurnClassification.lean)
-/
@[path]
private lemma fkRectBlackOrbitDirection_nonUturn_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {d : FKMedialBlackDart T}
  [NeZero (fkRectBlackOrbitList pairing d).length]
  {i : Fin (fkRectBlackOrbitList pairing d).length} :
-- imply
  fkRectBlackOrbitDirection pairing d (i + 1) ≠ fkRectBlackOrbitDirection pairing d i + 2 := by
-- proof
  apply StatMech.FrontierD.fkRectBlackOrbitDirection_nonUturn pairing d i

/--
[ons_three_le_of_two_le_of_closed_of_nonUturn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialLoopTurnClassification.lean)
-/
@[path]
private lemma ons_three_le_of_two_le_of_closed_of_nonUturn_eq
  {T : EvenTorus}
  {n : Nat}
  [NeZero n]
  {dir : Fin n → Fin 4}
-- given
  (htwo : 2 ≤ n)
  (hclosed : ons_pathDisplacement (List.ofFn dir) = 0)
  (hnu : ∀ i : Fin n, dir (i + 1) ≠ dir i + 2) :
-- imply
  3 ≤ n := by
-- proof
  apply StatMech.FrontierD.ons_three_le_of_two_le_of_closed_of_nonUturn dir htwo hclosed hnu

/--
[fkRectBlackOrbit_contractible_cyclicTurnSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialLoopTurnClassification.lean)
-/
@[path]
private lemma fkRectBlackOrbit_contractible_cyclicTurnSum_eq
  {T : EvenTorus}
  {R : FKRectTorus}
  {pairing : FKMedialLoopPairing R.medialTorus}
  {d : FKMedialBlackDart R.medialTorus}
-- given
  (hclosed : ons_pathDisplacement (List.ofFn (fkRectBlackOrbitDirection pairing d)) = 0) :
-- imply
  ons_cyclicTurnSum (List.ofFn (fkRectBlackOrbitDirection pairing d)) = 4 ∨ ons_cyclicTurnSum (List.ofFn (fkRectBlackOrbitDirection pairing d)) = -4 := by
-- proof
  apply StatMech.FrontierD.fkRectBlackOrbit_contractible_cyclicTurnSum R pairing d hclosed

/--
[fkRectBlackOrbit_periodState_exists_shiftedPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialLoopTurnClassification.lean)
-/
@[path]
private lemma fkRectBlackOrbit_periodState_exists_shiftedPoint_eq
  {T : EvenTorus}
  {R : FKRectTorus}
  {pairing : FKMedialLoopPairing R.medialTorus}
  {d : FKMedialBlackDart R.medialTorus}
  [NeZero (fkRectBlackOrbitList pairing d).length]
  {z : Nat × Fin (fkRectBlackOrbitList pairing d).length} :
-- imply
  ∃ u : Int × Int, fkRectBlackDartShiftedPoint R u ((fkMedialBlackBoundaryPerm pairing)^[z.2.val] d) = fkRectBlackBoundaryPointAfter R pairing d 0 + 2 • ons_periodStateCoord (fkRectBlackOrbitDirection pairing d) z := by
-- proof
  apply StatMech.FrontierD.fkRectBlackOrbit_periodState_exists_shiftedPoint R pairing d z

/--
[fkRectBlackOrbit_iterate_index_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialLoopTurnClassification.lean)
-/
@[path]
private lemma fkRectBlackOrbit_iterate_index_injective_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {d : FKMedialBlackDart T} :
-- imply
  Function.Injective (fun i : Fin (fkRectBlackOrbitList pairing d).length => (fkMedialBlackBoundaryPerm pairing)^[i.val] d) := by
-- proof
  apply StatMech.FrontierD.fkRectBlackOrbit_iterate_index_injective pairing d

/--
[fkRectBlackOrbit_periodStateCoord_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialLoopTurnClassification.lean)
-/
@[path]
private lemma fkRectBlackOrbit_periodStateCoord_injective_eq
  {T : EvenTorus}
  {R : FKRectTorus}
  {pairing : FKMedialLoopPairing R.medialTorus}
  {d : FKMedialBlackDart R.medialTorus}
  [NeZero (fkRectBlackOrbitList pairing d).length]
-- given
  (hne : (ons_pathDisplacement (List.ofFn (fkRectBlackOrbitDirection pairing d))).1 ≠ 0 ∨ (ons_pathDisplacement (List.ofFn (fkRectBlackOrbitDirection pairing d))).2 ≠ 0) :
-- imply
  Function.Injective (ons_periodStateCoord (fkRectBlackOrbitDirection pairing d)) := by
-- proof
  apply StatMech.FrontierD.fkRectBlackOrbit_periodStateCoord_injective R pairing d hne

/--
[fkRectBlackOrbit_cyclicTurnSum_classification](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialLoopTurnClassification.lean)
-/
@[path]
private lemma fkRectBlackOrbit_cyclicTurnSum_classification_eq
  {T : EvenTorus}
  {R : FKRectTorus}
  {pairing : FKMedialLoopPairing R.medialTorus}
  {d : FKMedialBlackDart R.medialTorus} :
-- imply
  ons_cyclicTurnSum (List.ofFn (fkRectBlackOrbitDirection pairing d)) = 0 ∨ ons_cyclicTurnSum (List.ofFn (fkRectBlackOrbitDirection pairing d)) = 4 ∨ ons_cyclicTurnSum (List.ofFn (fkRectBlackOrbitDirection pairing d)) = -4 := by
-- proof
  apply StatMech.FrontierD.fkRectBlackOrbit_cyclicTurnSum_classification R pairing d

/--
[fkRectBlackOrbitDirection_ofFn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialLoopTurnClassification.lean)
-/
@[path]
private lemma fkRectBlackOrbitDirection_ofFn_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {d : FKMedialBlackDart T} :
-- imply
  List.ofFn (fkRectBlackOrbitDirection pairing d) = (fkRectBlackOrbitList pairing d).map (fun e : FKMedialBlackDart T => fkMedialStrandDirection pairing e.1) := by
-- proof
  apply StatMech.FrontierD.fkRectBlackOrbitDirection_ofFn pairing d

/--
[fkRectBlackOrbit_cyclicTurnSum_classification_toList](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialLoopTurnClassification.lean)
-/
@[path]
private lemma fkRectBlackOrbit_cyclicTurnSum_classification_toList_eq
  {T : EvenTorus}
  {R : FKRectTorus}
  {pairing : FKMedialLoopPairing R.medialTorus}
  {d : FKMedialBlackDart R.medialTorus} :
-- imply
  ons_cyclicTurnSum ((fkMedialBlackBoundaryPerm pairing).toList d |>.map (fun e : FKMedialBlackDart R.medialTorus => fkMedialStrandDirection pairing e.1)) = 0 ∨ ons_cyclicTurnSum ((fkMedialBlackBoundaryPerm pairing).toList d |>.map (fun e : FKMedialBlackDart R.medialTorus => fkMedialStrandDirection pairing e.1)) = 4 ∨ ons_cyclicTurnSum ((fkMedialBlackBoundaryPerm pairing).toList d |>.map (fun e : FKMedialBlackDart R.medialTorus => fkMedialStrandDirection pairing e.1)) = -4 := by
-- proof
  apply StatMech.FrontierD.fkRectBlackOrbit_cyclicTurnSum_classification_toList R pairing d

/--
[fkRectCanonicalComponentTurn_classification](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialLoopTurnClassification.lean)
-/
@[path]
private lemma fkRectCanonicalComponentTurn_classification_eq
  {T : EvenTorus}
  {R : FKRectTorus}
  {pairing : FKMedialLoopPairing R.medialTorus}
  {C : FKMedialLoop R.medialTorus pairing} :
-- imply
  canonicalComponentTurn pairing C = 0 ∨ canonicalComponentTurn pairing C = 4 ∨ canonicalComponentTurn pairing C = -4 := by
-- proof
  apply StatMech.FrontierD.fkRectCanonicalComponentTurn_classification R pairing C


-- created on 2026-10-23
