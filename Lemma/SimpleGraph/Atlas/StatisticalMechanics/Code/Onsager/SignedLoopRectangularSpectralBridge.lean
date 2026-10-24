import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Onsager.SignedLoopRectangularSpectralBridge
open Finset SimpleGraph StatMech StatMech.Onsager


/--
[ons_rectDual_dartVector_eq_kwRectilinearVector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopRectangularSpectralBridge.lean)
-/
@[path]
private lemma ons_rectDual_dartVector_eq_kwRectilinearVector_eq
  {M N : Nat}
  {dart : (ons_rectDualGraph M N).Dart} :
-- imply
  ons_rectDualComplexPoint dart.snd - ons_rectDualComplexPoint dart.fst = kwRectilinearVector (ons_rectDualDartDirection4 dart) := by
-- proof
  apply StatMech.Onsager.ons_rectDual_dartVector_eq_kwRectilinearVector dart

/--
[ons_rectDualDartDirection4_ne_opposite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopRectangularSpectralBridge.lean)
-/
@[path]
private lemma ons_rectDualDartDirection4_ne_opposite_eq
  {M N : Nat}
  {dart next : (ons_rectDualGraph M N).Dart}
-- given
  (hadj : (ons_rectDualGraph M N).DartAdj dart next)
  (hedge : dart.edge ≠ next.edge) :
-- imply
  ons_rectDualDartDirection4 next ≠ ons_rectDualDartDirection4 dart + 2 := by
-- proof
  apply StatMech.Onsager.ons_rectDualDartDirection4_ne_opposite dart next hadj hedge

/--
[ons_rectDualDartDirection4_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopRectangularSpectralBridge.lean)
-/
@[path]
private lemma ons_rectDualDartDirection4_symm_eq
  {M N : Nat}
  {dart : (ons_rectDualGraph M N).Dart} :
-- imply
  ons_rectDualDartDirection4 dart.symm = ons_rectDualDartDirection4 dart + 2 := by
-- proof
  apply StatMech.Onsager.ons_rectDualDartDirection4_symm dart

/--
[ons_rectDual_turnPhase_eq_turnW](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopRectangularSpectralBridge.lean)
-/
@[path]
private lemma ons_rectDual_turnPhase_eq_turnW_eq
  {M N : Nat}
  {dart next : (ons_rectDualGraph M N).Dart}
-- given
  (hadj : (ons_rectDualGraph M N).DartAdj dart next)
  (hedge : dart.edge ≠ next.edge) :
-- imply
  (ons_rectDualStraightLineEmbedding M N).turnPhase dart next = ons_turnW ons_turnRoot (ons_rectDualDartDirection4 dart) (ons_rectDualDartDirection4 next) := by
-- proof
  apply StatMech.Onsager.ons_rectDual_turnPhase_eq_turnW dart next hadj hedge

/--
[ons_rectDualVertexSlot_fst_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopRectangularSpectralBridge.lean)
-/
@[path]
private lemma ons_rectDualVertexSlot_fst_val_eq
  {M N : Nat}
  {vertex : ons_RectDualVertex M N} :
-- imply
  (ons_rectDualVertexSlot vertex).1.val = vertex.1.val := by
-- proof
  apply StatMech.Onsager.ons_rectDualVertexSlot_fst_val vertex

/--
[ons_rectDualVertexSlot_snd_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopRectangularSpectralBridge.lean)
-/
@[path]
private lemma ons_rectDualVertexSlot_snd_val_eq
  {M N : Nat}
  {vertex : ons_RectDualVertex M N} :
-- imply
  (ons_rectDualVertexSlot vertex).2.val = vertex.2.val := by
-- proof
  apply StatMech.Onsager.ons_rectDualVertexSlot_snd_val vertex

/--
[ons_rectDualVertexSlot_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopRectangularSpectralBridge.lean)
-/
@[path]
private lemma ons_rectDualVertexSlot_injective_eq
  {M N : Nat} :
-- imply
  Function.Injective (ons_rectDualVertexSlot : ons_RectDualVertex M N → ons_RectVertex M N) := by
-- proof
  apply StatMech.Onsager.ons_rectDualVertexSlot_injective

/--
[ons_rectDualDartSlot_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopRectangularSpectralBridge.lean)
-/
@[path]
private lemma ons_rectDualDartSlot_valid_eq
  {M N : Nat}
  {dart : (ons_rectDualGraph M N).Dart} :
-- imply
  ons_rectDartValid M N (ons_rectDualDartSlot dart) := by
-- proof
  apply StatMech.Onsager.ons_rectDualDartSlot_valid dart

/--
[ons_rectDualDartSlot_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopRectangularSpectralBridge.lean)
-/
@[path]
private lemma ons_rectDualDartSlot_injective_eq
  {M N : Nat} :
-- imply
  Function.Injective (ons_rectDualDartSlot : (ons_rectDualGraph M N).Dart → ons_RectDart M N) := by
-- proof
  apply StatMech.Onsager.ons_rectDualDartSlot_injective

/--
[ons_rectDualDartSlot_surjective_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopRectangularSpectralBridge.lean)
-/
@[path]
private lemma ons_rectDualDartSlot_surjective_valid_eq
  {M N : Nat}
  {slot : ons_RectDart M N}
-- given
  (hslot : ons_rectDartValid M N slot) :
-- imply
  ∃ dart : (ons_rectDualGraph M N).Dart, ons_rectDualDartSlot dart = slot := by
-- proof
  apply StatMech.Onsager.ons_rectDualDartSlot_surjective_valid slot hslot

/--
[ons_rectDualSlotWeight_dartSlot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopRectangularSpectralBridge.lean)
-/
@[path]
private lemma ons_rectDualSlotWeight_dartSlot_eq
  {M N : Nat}
  {edgeWeight : Sym2 (ons_RectDualVertex M N) → Complex}
  {dart : (ons_rectDualGraph M N).Dart} :
-- imply
  ons_rectDualSlotWeight M N edgeWeight (ons_rectDualDartSlot dart) = edgeWeight dart.edge := by
-- proof
  apply StatMech.Onsager.ons_rectDualSlotWeight_dartSlot M N edgeWeight dart

/--
[norm_ons_rectDualSlotWeight_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopRectangularSpectralBridge.lean)
-/
@[path]
private lemma norm_ons_rectDualSlotWeight_le_eq
  {M N : Nat}
  {edgeWeight : Sym2 (ons_RectDualVertex M N) → Complex}
  {q : Real}
  {slot : ons_RectDart M N}
-- given
  (hq : 0 ≤ q)
  (hweight : ∀ edge, ‖edgeWeight edge‖ ≤ q) :
-- imply
  ‖ons_rectDualSlotWeight M N edgeWeight slot‖ ≤ q := by
-- proof
  apply StatMech.Onsager.norm_ons_rectDualSlotWeight_le M N edgeWeight q hq hweight slot

/--
[ons_rectDualVertexSlot_snd_eq_rectDirStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopRectangularSpectralBridge.lean)
-/
@[path]
private lemma ons_rectDualVertexSlot_snd_eq_rectDirStep_eq
  {M N : Nat}
  {dart : (ons_rectDualGraph M N).Dart} :
-- imply
  ons_rectDualVertexSlot dart.snd = ons_rectDirStep M N (ons_rectDualDartDirection4 dart) (ons_rectDualVertexSlot dart.fst) := by
-- proof
  apply StatMech.Onsager.ons_rectDualVertexSlot_snd_eq_rectDirStep dart

/--
[ons_rectKWmatDartWeighted_apply_of_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopRectangularSpectralBridge.lean)
-/
@[path]
private lemma ons_rectKWmatDartWeighted_apply_of_valid_eq
  {M N : Nat}
  {weight : ons_RectDart M N → Complex}
  {next dart : ons_RectDart M N}
-- given
  (hnext : ons_rectDartValid M N next)
  (hdart : ons_rectDartValid M N dart) :
-- imply
  ons_rectKWmatDartWeighted M N weight next dart = if next.1 = ons_rectDirStep M N dart.2 dart.1 then ons_turnW ons_turnRoot dart.2 next.2 * weight dart else 0 := by
-- proof
  apply StatMech.Onsager.ons_rectKWmatDartWeighted_apply_of_valid M N weight next dart hnext hdart

/--
[ons_rectKWmatDartWeighted_apply_eq_zero_of_not_valid_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopRectangularSpectralBridge.lean)
-/
@[path]
private lemma ons_rectKWmatDartWeighted_apply_eq_zero_of_not_valid_right_eq
  {M N : Nat}
  {weight : ons_RectDart M N → Complex}
  {next dart : ons_RectDart M N}
-- given
  (hdart : ¬ons_rectDartValid M N dart) :
-- imply
  ons_rectKWmatDartWeighted M N weight next dart = 0 := by
-- proof
  apply StatMech.Onsager.ons_rectKWmatDartWeighted_apply_eq_zero_of_not_valid_right M N weight next dart hdart

/--
[ons_rectKWmatDartWeighted_apply_eq_zero_of_not_valid_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopRectangularSpectralBridge.lean)
-/
@[path]
private lemma ons_rectKWmatDartWeighted_apply_eq_zero_of_not_valid_left_eq
  {M N : Nat}
  {weight : ons_RectDart M N → Complex}
  {next dart : ons_RectDart M N}
-- given
  (hnext : ¬ons_rectDartValid M N next) :
-- imply
  ons_rectKWmatDartWeighted M N weight next dart = 0 := by
-- proof
  apply StatMech.Onsager.ons_rectKWmatDartWeighted_apply_eq_zero_of_not_valid_left M N weight next dart hnext

/--
[kwGraphTransition_canonical_eq_rectKWmatDartWeighted_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopRectangularSpectralBridge.lean)
-/
@[path]
private lemma kwGraphTransition_canonical_eq_rectKWmatDartWeighted_apply_eq
  {M N : Nat}
  {edgeWeight : Sym2 (ons_RectDualVertex M N) → Complex}
  {dartWeight : ons_RectDart M N → Complex}
  {dart next : (ons_rectDualGraph M N).Dart}
-- given
  (hweight : ∀ dart : (ons_rectDualGraph M N).Dart, dartWeight (ons_rectDualDartSlot dart) = edgeWeight dart.edge) :
-- imply
  kwGraphTransition (ons_rectDualGraph M N) edgeWeight (ons_rectDualStraightLineEmbedding M N).turnPhase dart next = ons_rectKWmatDartWeighted M N dartWeight (ons_rectDualDartSlot next) (ons_rectDualDartSlot dart) := by
-- proof
  apply StatMech.Onsager.kwGraphTransition_canonical_eq_rectKWmatDartWeighted_apply edgeWeight dartWeight hweight dart next

/--
[reindex_rectKWmatDartWeighted_eq_native_fromBlocks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopRectangularSpectralBridge.lean)
-/
@[path]
private lemma reindex_rectKWmatDartWeighted_eq_native_fromBlocks_eq
  {M N : Nat}
  {edgeWeight : Sym2 (ons_RectDualVertex M N) → Complex} :
-- imply
  (Matrix.reindex (ons_rectDualDartSumEquiv M N).symm (ons_rectDualDartSumEquiv M N).symm) (ons_rectKWmatDartWeighted M N (ons_rectDualSlotWeight M N edgeWeight)) = Matrix.fromBlocks (kwGraphTransition (ons_rectDualGraph M N) edgeWeight (ons_rectDualStraightLineEmbedding M N).turnPhase).transpose 0 0 0 := by
-- proof
  apply StatMech.Onsager.reindex_rectKWmatDartWeighted_eq_native_fromBlocks M N edgeWeight

/--
[rectKWmatDartWeighted_charpoly_eq_native_mul_X](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopRectangularSpectralBridge.lean)
-/
@[path]
private lemma rectKWmatDartWeighted_charpoly_eq_native_mul_X_eq
  {M N : Nat}
  {edgeWeight : Sym2 (ons_RectDualVertex M N) → Complex} :
-- imply
  (ons_rectKWmatDartWeighted M N (ons_rectDualSlotWeight M N edgeWeight)).charpoly = (kwGraphTransition (ons_rectDualGraph M N) edgeWeight (ons_rectDualStraightLineEmbedding M N).turnPhase).charpoly * Polynomial.X ^ Fintype.card {slot : ons_RectDart M N // ¬ons_rectDartValid M N slot} := by
-- proof
  apply StatMech.Onsager.rectKWmatDartWeighted_charpoly_eq_native_mul_X M N edgeWeight

/--
[rectKWmatDartWeighted_det_one_sub_eq_native](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopRectangularSpectralBridge.lean)
-/
@[path]
private lemma rectKWmatDartWeighted_det_one_sub_eq_native_eq
  {M N : Nat}
  {edgeWeight : Sym2 (ons_RectDualVertex M N) → Complex} :
-- imply
  (1 - ons_rectKWmatDartWeighted M N (ons_rectDualSlotWeight M N edgeWeight)).det = (1 - kwGraphTransition (ons_rectDualGraph M N) edgeWeight (ons_rectDualStraightLineEmbedding M N).turnPhase).det := by
-- proof
  apply StatMech.Onsager.rectKWmatDartWeighted_det_one_sub_eq_native M N edgeWeight

/--
[norm_root_kwGraphTransition_canonical_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopRectangularSpectralBridge.lean)
-/
@[path]
private lemma norm_root_kwGraphTransition_canonical_le_eq
  {M N : Nat}
  {edgeWeight : Sym2 (ons_RectDualVertex M N) → Complex}
  {q : Real}
  {alpha : Complex}
-- given
  (hq : 0 ≤ q)
  (hweight : ∀ edge, ‖edgeWeight edge‖ ≤ q)
  (halpha : alpha ∈ (kwGraphTransition (ons_rectDualGraph M N) edgeWeight (ons_rectDualStraightLineEmbedding M N).turnPhase).charpoly.roots) :
-- imply
  ‖alpha‖ ≤ (Real.sqrt 2 + 1) * q := by
-- proof
  apply StatMech.Onsager.norm_root_kwGraphTransition_canonical_le M N edgeWeight q hq hweight alpha halpha

/--
[kwGraphTransition_canonical_spectral](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopRectangularSpectralBridge.lean)
-/
@[path]
private lemma kwGraphTransition_canonical_spectral_eq
  {M N : Nat}
  {edgeWeight : Sym2 (ons_RectDualVertex M N) → Complex}
  {q : Real}
-- given
  (hq0 : 0 ≤ q)
  (hq : q < ons_signedLoopCriticalWeight)
  (hweight : ∀ edge, ‖edgeWeight edge‖ ≤ q) :
-- imply
  ∀ alpha ∈ (kwGraphTransition (ons_rectDualGraph M N) edgeWeight (ons_rectDualStraightLineEmbedding M N).turnPhase).charpoly.roots, ‖alpha‖ < 1 := by
-- proof
  apply StatMech.Onsager.kwGraphTransition_canonical_spectral M N edgeWeight q hq0 hq hweight

/--
[kwGraphTransition_canonical_det_eq_walk_exp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopRectangularSpectralBridge.lean)
-/
@[path]
private lemma kwGraphTransition_canonical_det_eq_walk_exp_eq
  {M N : Nat}
  {edgeWeight : Sym2 (ons_RectDualVertex M N) → Complex}
  {q : Real}
-- given
  (hq0 : 0 ≤ q)
  (hq : q < ons_signedLoopCriticalWeight)
  (hweight : ∀ edge, ‖edgeWeight edge‖ ≤ q) :
-- imply
  (1 - kwGraphTransition (ons_rectDualGraph M N) edgeWeight (ons_rectDualStraightLineEmbedding M N).turnPhase).det = Complex.exp (-∑' n : Nat, (∑ walk : Fin (n + 1) → (ons_rectDualGraph M N).Dart, ∏ k : Fin (n + 1), kwGraphTransition (ons_rectDualGraph M N) edgeWeight (ons_rectDualStraightLineEmbedding M N).turnPhase (walk k) (walk (k + 1))) / (n + 1)) := by
-- proof
  apply StatMech.Onsager.kwGraphTransition_canonical_det_eq_walk_exp M N edgeWeight q hq0 hq hweight

/--
[norm_ons_rectDualEdgeSignDefect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopRectangularSpectralBridge.lean)
-/
@[path]
private lemma norm_ons_rectDualEdgeSignDefect_eq
  {M N : Nat}
  [DecidablePred defect]
  {q : Real}
  {edge : Sym2 (ons_RectDualVertex M N)}
-- given
  (defect : Sym2 (ons_RectDualVertex M N) → Prop)
  (hq : 0 ≤ q) :
-- imply
  ‖ons_rectDualEdgeSignDefect M N defect q edge‖ = q := by
-- proof
  apply StatMech.Onsager.norm_ons_rectDualEdgeSignDefect M N defect hq edge

/--
[ons_rectDualSignDefect_det_ratio_eq_walk_exp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopRectangularSpectralBridge.lean)
-/
@[path]
private lemma ons_rectDualSignDefect_det_ratio_eq_walk_exp_eq
  {M N : Nat}
  [DecidablePred defect]
  {q : Real}
-- given
  (defect : Sym2 (ons_RectDualVertex M N) → Prop)
  (hq0 : 0 ≤ q)
  (hq : q < ons_signedLoopCriticalWeight) :
-- imply
  (1 - kwGraphTransition (ons_rectDualGraph M N) (ons_rectDualEdgeSignDefect M N defect q) (ons_rectDualStraightLineEmbedding M N).turnPhase).det / (1 - kwGraphTransition (ons_rectDualGraph M N) (fun _ ↦ (q : Complex)) (ons_rectDualStraightLineEmbedding M N).turnPhase).det = Complex.exp (-(ons_rectDualWalkExponent M N (ons_rectDualEdgeSignDefect M N defect q) - ons_rectDualWalkExponent M N (fun _ ↦ (q : Complex)))) := by
-- proof
  apply StatMech.Onsager.ons_rectDualSignDefect_det_ratio_eq_walk_exp M N defect q hq0 hq


-- created on 2026-10-23
