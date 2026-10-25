import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalFirstReturn.Part20
open StatMech StatMech.Onsager StatMech.Onsager.DecFormalExpAdd


/--
[ons_invariantMarkedTerm_eq_rerootTerm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_invariantMarkedTerm_eq_rerootTerm_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  [NeZero n]
  {weight : (Fin n → E) → ℂ}
  {e r : E}
  {k : Fin n}
  {loop : Fin n → E}
-- given
  (hrotate : ∀ k loop, weight (ons_rotate k loop) = weight loop) :
-- imply
  ons_invariantMarkedTerm weight e r k loop = ons_invariantRerootTerm weight e r (ons_rotate k loop) := by
-- proof
  apply StatMech.Onsager.ons_invariantMarkedTerm_eq_rerootTerm weight hrotate e r k loop

/--
[ons_sum_invariantMarkedTerm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_sum_invariantMarkedTerm_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  [NeZero n]
  {weight : (Fin n → E) → ℂ}
  {e r : E}
  {k : Fin n}
-- given
  (hrotate : ∀ k loop, weight (ons_rotate k loop) = weight loop) :
-- imply
  ∑ loop : Fin n → E, ons_invariantMarkedTerm weight e r k loop = ∑ loop : Fin n → E, ons_invariantRerootTerm weight e r loop := by
-- proof
  apply StatMech.Onsager.ons_sum_invariantMarkedTerm weight hrotate e r k

/--
[ons_sum_invariantMarks_recovers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_sum_invariantMarks_recovers_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  [NeZero n]
  {weight : (Fin n → E) → ℂ}
  {e r : E}
  {loop : Fin n → E} :
-- imply
  (∑ k : Fin n, ons_invariantMarkedTerm weight e r k loop) = if (∀ j, loop j ≠ r) ∧ (∃ k, loop k = e) then weight loop else 0 := by
-- proof
  apply StatMech.Onsager.ons_sum_invariantMarks_recovers weight e r loop

/--
[ons_sum_div_length_eq_rerooted_of_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_sum_div_length_eq_rerooted_of_invariant_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  [NeZero n]
  {weight : (Fin n → E) → ℂ}
  {e r : E}
-- given
  (hrotate : ∀ k loop, weight (ons_rotate k loop) = weight loop) :
-- imply
  (∑ loop ∈ Finset.univ.filter (fun loop : Fin n → E ↦ (∃ k, loop k = e) ∧ ∀ j, loop j ≠ r), weight loop) / (n : ℂ) = ∑ loop ∈ Finset.univ.filter (fun loop : Fin n → E ↦ loop 0 = e ∧ ∀ j, loop j ≠ r), weight loop / (ons_visitCount e loop : ℂ) := by
-- proof
  apply StatMech.Onsager.ons_sum_div_length_eq_rerooted_of_invariant weight hrotate e r

/--
[ons_decFixedExponentTerm_rotate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_decFixedExponentTerm_rotate_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {n : ℕ}
  [NeZero n]
  {m : ons_DecEdge L →₀ ℕ}
  {k : Fin n}
  {loop : Fin n → ons_Dart L} :
-- imply
  (if ons_decLoopExponent L (ons_rotate k loop) = m then ons_decLoopScalar L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b) (ons_rotate k loop) else 0) = if ons_decLoopExponent L loop = m then ons_decLoopScalar L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b) loop else 0 := by
-- proof
  apply StatMech.Onsager.ons_decFixedExponentTerm_rotate L a b m k loop

/--
[ons_decFormalFixedBucketE_div_eq_rerooted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_decFormalFixedBucketE_div_eq_rerooted_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {d : ons_Dart L}
  {r : ℕ}
  {m : ons_DecEdge L →₀ ℕ} :
-- imply
  ons_decFormalFixedBucketE L a b d r m / ((r : ℂ) + 1) = ∑ loop ∈ Finset.univ.filter (fun loop : Fin (r + 1) → ons_Dart L ↦ loop 0 = d ∧ ∀ j, loop j ≠ ons_dartRev L d), (if ons_decLoopExponent L loop = m then ons_decLoopScalar L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b) loop else 0) / (ons_visitCount d loop : ℂ) := by
-- proof
  apply StatMech.Onsager.ons_decFormalFixedBucketE_div_eq_rerooted L a b d r m

/--
[ons_pathSum_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_pathSum_nil_eq
  [AddCommMonoid M]
  {step : E → E → M} :
-- imply
  ons_pathSum step [] = 0 := by
-- proof
  apply StatMech.Onsager.ons_pathSum_nil step

/--
[ons_pathSum_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_pathSum_singleton_eq
  [AddCommMonoid M]
  {step : E → E → M}
  {x : E} :
-- imply
  ons_pathSum step [x] = 0 := by
-- proof
  apply StatMech.Onsager.ons_pathSum_singleton step x

/--
[ons_pathSum_cons_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_pathSum_cons_cons_eq
  [AddCommMonoid M]
  {step : E → E → M}
  {x y : E}
  {tail : List E} :
-- imply
  ons_pathSum step (x :: y :: tail) = step x y + ons_pathSum step (y :: tail) := by
-- proof
  apply StatMech.Onsager.ons_pathSum_cons_cons step x y tail

/--
[ons_pathSum_append_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_pathSum_append_cons_eq
  [AddCommMonoid M]
  {step : E → E → M}
  {pre : List E}
  {x : E}
  {suffix : List E} :
-- imply
  ons_pathSum step (pre ++ x :: suffix) = ons_pathSum step (pre ++ [x]) + ons_pathSum step (x :: suffix) := by
-- proof
  apply StatMech.Onsager.ons_pathSum_append_cons step pre x suffix

/--
[ons_pathSum_glue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_pathSum_glue_eq
  [AddCommMonoid M]
  {step : E → E → M}
  {root : E}
  {segments : List (List E)}
-- given
  (hhead : ∀ segment ∈ segments, segment.head? = some root)
  (hlast : ∀ segment ∈ segments, segment.getLast? = some root) :
-- imply
  ons_pathSum step (ons_glue root segments) = (segments.map (ons_pathSum step)).sum := by
-- proof
  apply StatMech.Onsager.ons_pathSum_glue step root segments hhead hlast

/--
[ons_pathSum_ofFn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_pathSum_ofFn_eq
  [AddCommMonoid M]
  {step : E → E → M}
  {n : ℕ}
  {f : Fin (n + 1) → E} :
-- imply
  ons_pathSum step (List.ofFn f) = ∑ i : Fin n, step (f i.castSucc) (f i.succ) := by
-- proof
  apply StatMech.Onsager.ons_pathSum_ofFn step n f

/--
[ons_cyclicSum_eq_pathSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_cyclicSum_eq_pathSum_eq
  [AddCommMonoid M]
  {step : E → E → M}
  {n : ℕ}
  {loop : Fin (n + 1) → E} :
-- imply
  (∑ k, step (loop k) (loop (k + 1))) = ons_pathSum step (List.ofFn loop ++ [loop 0]) := by
-- proof
  apply StatMech.Onsager.ons_cyclicSum_eq_pathSum step loop

/--
[ons_decLoopExponent_eq_pathSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_decLoopExponent_eq_pathSum_eq
  {L : ℕ}
  {n : ℕ}
  {loop : Fin (n + 1) → ons_Dart L} :
-- imply
  ons_decLoopExponent L loop = ons_pathSum (ons_decTransitionExponent L) (List.ofFn loop ++ [loop 0]) := by
-- proof
  apply StatMech.Onsager.ons_decLoopExponent_eq_pathSum L loop

/--
[ons_decLoopExponent_eq_firstReturnFactors_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_decLoopExponent_eq_firstReturnFactors_sum_eq
  {L : ℕ}
  {n : ℕ}
  {d : ons_Dart L}
  {loop : Fin (n + 1) → ons_Dart L}
-- given
  (hroot : loop 0 = d) :
-- imply
  ons_decLoopExponent L loop = ((ons_firstReturnFactors d (List.ofFn loop ++ [d])).map (ons_pathSum (ons_decTransitionExponent L))).sum := by
-- proof
  apply StatMech.Onsager.ons_decLoopExponent_eq_firstReturnFactors_sum L d loop hroot

/--
[ons_decLoopScalar_eq_firstReturnFactors_prod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_decLoopScalar_eq_firstReturnFactors_prod_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {n : ℕ}
  {d : ons_Dart L}
  {loop : Fin (n + 1) → ons_Dart L}
-- given
  (hroot : loop 0 = d) :
-- imply
  ons_decLoopScalar L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b) loop = ((ons_firstReturnFactors d (List.ofFn loop ++ [d])).map (ons_edgeWeight (ons_KWmatWeightedPhase L (fun _ ↦ 1) ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)))).prod := by
-- proof
  apply StatMech.Onsager.ons_decLoopScalar_eq_firstReturnFactors_prod L a b d loop hroot

/--
[ons_firstReturnSegment_eq_closedFinLoop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_firstReturnSegment_eq_closedFinLoop_eq
  {d : E}
  {segment : List E}
-- given
  (hsegment : ons_isFirstReturnSegment d segment) :
-- imply
  ∃ (n : ℕ) (loop : Fin (n + 1) → E), loop 0 = d ∧ (∀ k, k ≠ 0 → loop k ≠ d) ∧ segment = List.ofFn loop ++ [d] := by
-- proof
  apply StatMech.Onsager.ons_firstReturnSegment_eq_closedFinLoop hsegment

/--
[ons_closedFinLoop_isFirstReturnSegment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_closedFinLoop_isFirstReturnSegment_eq
  {n : ℕ}
  {d : E}
  {loop : Fin (n + 1) → E}
-- given
  (hroot : loop 0 = d)
  (hfirst : ∀ k, k ≠ 0 → loop k ≠ d) :
-- imply
  ons_isFirstReturnSegment d (List.ofFn loop ++ [d]) := by
-- proof
  apply StatMech.Onsager.ons_closedFinLoop_isFirstReturnSegment loop hroot hfirst

/--
[ons_firstReturnSegment_avoids_of_closedLoop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_firstReturnSegment_avoids_of_closedLoop_eq
  {L n : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {loop : Fin (n + 1) → ons_Dart L}
-- given
  (havoid : ∀ k, loop k ≠ ons_dartRev L d) :
-- imply
  ∀ x ∈ List.ofFn loop ++ [d], x ≠ ons_dartRev L d := by
-- proof
  apply StatMech.Onsager.ons_firstReturnSegment_avoids_of_closedLoop d loop havoid

/--
[ons_decFirstReturnSegment_pathSum_eq_loopExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_decFirstReturnSegment_pathSum_eq_loopExponent_eq
  {L : ℕ}
  {n : ℕ}
  {d : ons_Dart L}
  {loop : Fin (n + 1) → ons_Dart L}
-- given
  (hroot : loop 0 = d) :
-- imply
  ons_pathSum (ons_decTransitionExponent L) (List.ofFn loop ++ [d]) = ons_decLoopExponent L loop := by
-- proof
  apply StatMech.Onsager.ons_decFirstReturnSegment_pathSum_eq_loopExponent L d loop hroot

/--
[ons_decFirstReturnSegment_edgeWeight_eq_loopScalar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_decFirstReturnSegment_edgeWeight_eq_loopScalar_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {n : ℕ}
  {d : ons_Dart L}
  {loop : Fin (n + 1) → ons_Dart L}
-- given
  (hroot : loop 0 = d) :
-- imply
  ons_edgeWeight (ons_KWmatWeightedPhase L (fun _ ↦ 1) ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) (List.ofFn loop ++ [d]) = ons_decLoopScalar L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b) loop := by
-- proof
  apply StatMech.Onsager.ons_decFirstReturnSegment_edgeWeight_eq_loopScalar L a b d loop hroot

/--
[ons_decFirstReturnAtomSegment_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_decFirstReturnAtomSegment_valid_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {atom : ons_DecFirstReturnAtom L d} :
-- imply
  ons_isFirstReturnSegment d (ons_decFirstReturnAtomSegment atom) ∧ ∀ x ∈ ons_decFirstReturnAtomSegment atom, x ≠ ons_dartRev L d := by
-- proof
  apply StatMech.Onsager.ons_decFirstReturnAtomSegment_valid atom

/--
[ons_decFirstReturnAtomSegment_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_decFirstReturnAtomSegment_injective_eq
  {L : ℕ}
  {d : ons_Dart L} :
-- imply
  Function.Injective (ons_decFirstReturnAtomSegment : ons_DecFirstReturnAtom L d → List (ons_Dart L)) := by
-- proof
  apply StatMech.Onsager.ons_decFirstReturnAtomSegment_injective

/--
[ons_decFirstReturnAtomSegment_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_decFirstReturnAtomSegment_surjective_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L} :
-- imply
  Function.Surjective (fun atom : ons_DecFirstReturnAtom L d ↦ (⟨ons_decFirstReturnAtomSegment atom, ons_decFirstReturnAtomSegment_valid atom⟩ : {segment : List (ons_Dart L) // ons_isFirstReturnSegment d segment ∧ ∀ x ∈ segment, x ≠ ons_dartRev L d})) := by
-- proof
  apply StatMech.Onsager.ons_decFirstReturnAtomSegment_surjective

/--
[ons_decFirstReturnAtomEquivSegment_apply_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_decFirstReturnAtomEquivSegment_apply_val_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {atom : ons_DecFirstReturnAtom L d} :
-- imply
  (ons_decFirstReturnAtomEquivSegment L d atom).1 = ons_decFirstReturnAtomSegment atom := by
-- proof
  apply StatMech.Onsager.ons_decFirstReturnAtomEquivSegment_apply_val L d atom

/--
[ons_decFirstReturnAtom_exponent_segment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_decFirstReturnAtom_exponent_segment_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {atom : ons_DecFirstReturnAtom L d} :
-- imply
  ons_pathSum (ons_decTransitionExponent L) (ons_decFirstReturnAtomSegment atom) = ons_decLoopExponent L atom.2.1 := by
-- proof
  apply StatMech.Onsager.ons_decFirstReturnAtom_exponent_segment L d atom

/--
[ons_decFirstReturnAtom_weight_segment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_decFirstReturnAtom_weight_segment_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {d : ons_Dart L}
  {atom : ons_DecFirstReturnAtom L d} :
-- imply
  ons_edgeWeight (ons_KWmatWeightedPhase L (fun _ ↦ 1) ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) (ons_decFirstReturnAtomSegment atom) = ons_decLoopScalar L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b) atom.2.1 := by
-- proof
  apply StatMech.Onsager.ons_decFirstReturnAtom_weight_segment L a b d atom

/--
[ons_decFirstReturnSegmentAtom_segment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_decFirstReturnSegmentAtom_segment_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {segment : List (ons_Dart L)}
-- given
  (hsegment : ons_isFirstReturnSegment d segment ∧ ∀ x ∈ segment, x ≠ ons_dartRev L d) :
-- imply
  ons_decFirstReturnAtomSegment (ons_decFirstReturnSegmentAtom L d segment) = segment := by
-- proof
  apply StatMech.Onsager.ons_decFirstReturnSegmentAtom_segment L d segment hsegment

/--
[ons_decFirstReturnAtomsSegments_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_decFirstReturnAtomsSegments_valid_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {atoms : List (ons_DecFirstReturnAtom L d)} :
-- imply
  ons_validFactorList d (ons_dartRev L d) (ons_decFirstReturnAtomsSegments d atoms) := by
-- proof
  apply StatMech.Onsager.ons_decFirstReturnAtomsSegments_valid L d atoms

/--
[ons_decFirstReturnAtomsSegments_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_decFirstReturnAtomsSegments_injective_eq
  {L : ℕ}
  {d : ons_Dart L} :
-- imply
  Function.Injective (ons_decFirstReturnAtomsSegments d : List (ons_DecFirstReturnAtom L d) → List (List (ons_Dart L))) := by
-- proof
  apply StatMech.Onsager.ons_decFirstReturnAtomsSegments_injective

/--
[ons_decFirstReturnAtomsSegments_surjective_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_decFirstReturnAtomsSegments_surjective_valid_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {segments : List (List (ons_Dart L))}
-- given
  (hsegments : ons_validFactorList d (ons_dartRev L d) segments) :
-- imply
  ∃ atoms : List (ons_DecFirstReturnAtom L d), ons_decFirstReturnAtomsSegments d atoms = segments := by
-- proof
  apply StatMech.Onsager.ons_decFirstReturnAtomsSegments_surjective_valid L d segments hsegments

/--
[ons_decFirstReturnAtomsEquivFactorList_apply_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_decFirstReturnAtomsEquivFactorList_apply_val_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {atoms : List (ons_DecFirstReturnAtom L d)} :
-- imply
  (ons_decFirstReturnAtomsEquivFactorList L d atoms).1 = ons_decFirstReturnAtomsSegments d atoms := by
-- proof
  apply StatMech.Onsager.ons_decFirstReturnAtomsEquivFactorList_apply_val L d atoms

/--
[ons_decRootedAtomList_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_decRootedAtomList_valid_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {atom : ons_DecRootedAtom L d} :
-- imply
  ons_validRootedList d (ons_dartRev L d) (ons_decRootedAtomList atom) ∧ 2 ≤ (ons_decRootedAtomList atom).length := by
-- proof
  apply StatMech.Onsager.ons_decRootedAtomList_valid L d atom

/--
[ons_decRootedAtomList_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_decRootedAtomList_injective_eq
  {L : ℕ}
  {d : ons_Dart L} :
-- imply
  Function.Injective (ons_decRootedAtomList : ons_DecRootedAtom L d → List (ons_Dart L)) := by
-- proof
  apply StatMech.Onsager.ons_decRootedAtomList_injective

/--
[ons_validRootedList_eq_closedFinLoop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_validRootedList_eq_closedFinLoop_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {w : List (ons_Dart L)}
-- given
  (hw : ons_validRootedList d (ons_dartRev L d) w)
  (hlength : 2 ≤ w.length) :
-- imply
  ∃ atom : ons_DecRootedAtom L d, ons_decRootedAtomList atom = w := by
-- proof
  apply StatMech.Onsager.ons_validRootedList_eq_closedFinLoop w hw hlength

/--
[ons_decRootedAtomEquivRootedList_apply_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_decRootedAtomEquivRootedList_apply_val_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {atom : ons_DecRootedAtom L d} :
-- imply
  (ons_decRootedAtomEquivRootedList L d atom).1 = ons_decRootedAtomList atom := by
-- proof
  apply StatMech.Onsager.ons_decRootedAtomEquivRootedList_apply_val L d atom

/--
[ons_firstReturnFactors_eq_nil_iff_rooted_eq_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_firstReturnFactors_eq_nil_iff_rooted_eq_singleton_eq
  [DecidableEq E]
  {e r : E}
  {w : List E}
-- given
  (hw : ons_validRootedList e r w) :
-- imply
  ons_firstReturnFactors e w = [] ↔ w = [e] := by
-- proof
  apply StatMech.Onsager.ons_firstReturnFactors_eq_nil_iff_rooted_eq_singleton e r w hw

/--
[ons_rootedList_nontrivial_iff_factors_ne_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_rootedList_nontrivial_iff_factors_ne_nil_eq
  [DecidableEq E]
  {e r : E}
  {w : List E}
-- given
  (hw : ons_validRootedList e r w) :
-- imply
  2 ≤ w.length ↔ ons_firstReturnFactors e w ≠ [] := by
-- proof
  apply StatMech.Onsager.ons_rootedList_nontrivial_iff_factors_ne_nil e r w hw

/--
[ons_decRootedAtomEquivNonemptyAtoms_segments](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_decRootedAtomEquivNonemptyAtoms_segments_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {root : ons_DecRootedAtom L d} :
-- imply
  ons_decFirstReturnAtomsSegments d (ons_decRootedAtomEquivNonemptyAtoms L d root).1 = ons_firstReturnFactors d (ons_decRootedAtomList root) := by
-- proof
  apply StatMech.Onsager.ons_decRootedAtomEquivNonemptyAtoms_segments L d root

/--
[ons_decRootedAtomExponent_eq_atoms_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_decRootedAtomExponent_eq_atoms_sum_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {root : ons_DecRootedAtom L d} :
-- imply
  ons_decRootedAtomExponent root = ((ons_decRootedAtomEquivNonemptyAtoms L d root).1.map ons_decFirstReturnAtomExponent).sum := by
-- proof
  apply StatMech.Onsager.ons_decRootedAtomExponent_eq_atoms_sum L d root

/--
[ons_decRootedAtomWeight_eq_atoms_prod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_decRootedAtomWeight_eq_atoms_prod_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {d : ons_Dart L}
  {root : ons_DecRootedAtom L d} :
-- imply
  ons_decRootedAtomWeight L a b root = ((ons_decRootedAtomEquivNonemptyAtoms L d root).1.map (ons_decFirstReturnAtomWeight L a b)).prod := by
-- proof
  apply StatMech.Onsager.ons_decRootedAtomWeight_eq_atoms_prod L a b d root

/--
[ons_decRootedAtom_atoms_length_eq_visitCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_decRootedAtom_atoms_length_eq_visitCount_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {root : ons_DecRootedAtom L d} :
-- imply
  (ons_decRootedAtomEquivNonemptyAtoms L d root).1.length = ons_visitCount d root.2.1 := by
-- proof
  apply StatMech.Onsager.ons_decRootedAtom_atoms_length_eq_visitCount L d root

/--
[ons_decRootedAtom_externalExponent_eq_visitCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_decRootedAtom_externalExponent_eq_visitCount_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {root : ons_DecRootedAtom L d} :
-- imply
  ons_decRootedAtomExponent root s(d, ons_dartRev L d) = ons_visitCount d root.2.1 := by
-- proof
  apply StatMech.Onsager.ons_decRootedAtom_externalExponent_eq_visitCount L d root

/--
[ons_decFormalFirstReturnCoeff_eq_sum_boundedAtoms](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_decFormalFirstReturnCoeff_eq_sum_boundedAtoms_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {d : ons_Dart L}
  {m : ons_DecEdge L →₀ ℕ} :
-- imply
  ons_decFormalFirstReturnCoeff L a b d m = ∑ atom : ons_DecFirstReturnAtomBounded L d (ons_finsuppTotalDegree m), if ons_decBoundedAtomExponent atom = m then ons_decBoundedAtomWeight L a b atom else 0 := by
-- proof
  apply StatMech.Onsager.ons_decFormalFirstReturnCoeff_eq_sum_boundedAtoms L a b d m

/--
[ons_decFormalFirstReturnCoeff_eq_sum_boundedAtoms_of_degree_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_decFormalFirstReturnCoeff_eq_sum_boundedAtoms_of_degree_le_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {d : ons_Dart L}
  {m : ons_DecEdge L →₀ ℕ}
  {N : ℕ}
-- given
  (hdegree : ons_finsuppTotalDegree m ≤ N) :
-- imply
  ons_decFormalFirstReturnCoeff L a b d m = ∑ atom : ons_DecFirstReturnAtomBounded L d N, if ons_decBoundedAtomExponent atom = m then ons_decBoundedAtomWeight L a b atom else 0 := by
-- proof
  apply StatMech.Onsager.ons_decFormalFirstReturnCoeff_eq_sum_boundedAtoms_of_degree_le L a b d m N hdegree

/--
[ons_decFormalFirstReturnTrunc_coeff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_decFormalFirstReturnTrunc_coeff_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {d : ons_Dart L}
  {N : ℕ}
  {m : ons_DecEdge L →₀ ℕ} :
-- imply
  MvPowerSeries.coeff m (ons_decFormalFirstReturnTrunc L a b d N) = ∑ atom : ons_DecFirstReturnAtomBounded L d N, if ons_decBoundedAtomExponent atom = m then ons_decBoundedAtomWeight L a b atom else 0 := by
-- proof
  apply StatMech.Onsager.ons_decFormalFirstReturnTrunc_coeff L a b d N m

/--
[ons_decFormalFirstReturn_coeff_eq_trunc_of_degree_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_decFormalFirstReturn_coeff_eq_trunc_of_degree_le_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {d : ons_Dart L}
  {m : ons_DecEdge L →₀ ℕ}
  {N : ℕ}
-- given
  (hdegree : ons_finsuppTotalDegree m ≤ N) :
-- imply
  MvPowerSeries.coeff m (ons_decFormalFirstReturn L a b d) = MvPowerSeries.coeff m (ons_decFormalFirstReturnTrunc L a b d N) := by
-- proof
  apply StatMech.Onsager.ons_decFormalFirstReturn_coeff_eq_trunc_of_degree_le L a b d m N hdegree

/--
[ons_finsuppTotalDegree_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_finsuppTotalDegree_mono_eq
  [DecidableEq E]
  {m n : E →₀ ℕ}
-- given
  (h : m ≤ n) :
-- imply
  ons_finsuppTotalDegree m ≤ ons_finsuppTotalDegree n := by
-- proof
  apply StatMech.Onsager.ons_finsuppTotalDegree_mono h

/--
[ons_decFormalFirstReturn_coeff_pow_eq_trunc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_decFormalFirstReturn_coeff_pow_eq_trunc_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {d : ons_Dart L}
  {m : ons_DecEdge L →₀ ℕ}
  {k : ℕ} :
-- imply
  MvPowerSeries.coeff m (ons_decFormalFirstReturn L a b d ^ k) = MvPowerSeries.coeff m (ons_decFormalFirstReturnTrunc L a b d (ons_finsuppTotalDegree m) ^ k) := by
-- proof
  apply StatMech.Onsager.ons_decFormalFirstReturn_coeff_pow_eq_trunc L a b d m k

/--
[ons_decFormalFirstReturnTrunc_coeff_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_decFormalFirstReturnTrunc_coeff_pow_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {d : ons_Dart L}
  {N k : ℕ}
  {m : ons_DecEdge L →₀ ℕ} :
-- imply
  MvPowerSeries.coeff m (ons_decFormalFirstReturnTrunc L a b d N ^ k) = ∑ atoms : Fin k → ons_DecFirstReturnAtomBounded L d N, if (∑ i, ons_decBoundedAtomExponent (atoms i)) = m then ∏ i, ons_decBoundedAtomWeight L a b (atoms i) else 0 := by
-- proof
  apply StatMech.Onsager.ons_decFormalFirstReturnTrunc_coeff_pow L a b d N k m

/--
[ons_decFormalFirstReturn_coeff_pow_eq_boundedTupleSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_decFormalFirstReturn_coeff_pow_eq_boundedTupleSum_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {d : ons_Dart L}
  {m : ons_DecEdge L →₀ ℕ}
  {k : ℕ} :
-- imply
  MvPowerSeries.coeff m (ons_decFormalFirstReturn L a b d ^ k) = ∑ atoms : Fin k → ons_DecFirstReturnAtomBounded L d (ons_finsuppTotalDegree m), if (∑ i, ons_decBoundedAtomExponent (atoms i)) = m then ∏ i, ons_decBoundedAtomWeight L a b (atoms i) else 0 := by
-- proof
  apply StatMech.Onsager.ons_decFormalFirstReturn_coeff_pow_eq_boundedTupleSum L a b d m k

/--
[ons_decFirstReturnAtom_externalExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_decFirstReturnAtom_externalExponent_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {atom : ons_DecFirstReturnAtom L d} :
-- imply
  ons_decFirstReturnAtomExponent atom s(d, ons_dartRev L d) = 1 := by
-- proof
  apply StatMech.Onsager.ons_decFirstReturnAtom_externalExponent L d atom

/--
[ons_decFirstReturnAtoms_externalExponent_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_decFirstReturnAtoms_externalExponent_sum_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {atoms : List (ons_DecFirstReturnAtom L d)} :
-- imply
  (atoms.map ons_decFirstReturnAtomExponent).sum s(d, ons_dartRev L d) = atoms.length := by
-- proof
  apply StatMech.Onsager.ons_decFirstReturnAtoms_externalExponent_sum L d atoms

/--
[ons_decForgetBoundedAtom_exponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_decForgetBoundedAtom_exponent_eq
  {L N : ℕ}
  {d : ons_Dart L}
  {atom : ons_DecFirstReturnAtomBounded L d N} :
-- imply
  ons_decFirstReturnAtomExponent (ons_decForgetBoundedAtom atom) = ons_decBoundedAtomExponent atom := by
-- proof
  apply StatMech.Onsager.ons_decForgetBoundedAtom_exponent atom

/--
[ons_decForgetBoundedAtom_weight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_decForgetBoundedAtom_weight_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {N : ℕ}
  {d : ons_Dart L}
  {atom : ons_DecFirstReturnAtomBounded L d N} :
-- imply
  ons_decFirstReturnAtomWeight L a b (ons_decForgetBoundedAtom atom) = ons_decBoundedAtomWeight L a b atom := by
-- proof
  apply StatMech.Onsager.ons_decForgetBoundedAtom_weight L a b atom

/--
[ons_decBoundedTupleToUnbounded_bijective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_decBoundedTupleToUnbounded_bijective_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {m : ons_DecEdge L →₀ ℕ} :
-- imply
  Function.Bijective (ons_decBoundedTupleToUnbounded L d m) := by
-- proof
  apply StatMech.Onsager.ons_decBoundedTupleToUnbounded_bijective L d m

/--
[ons_decForgetBoundedRoot_exponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_decForgetBoundedRoot_exponent_eq
  {L N : ℕ}
  {d : ons_Dart L}
  {root : ons_DecRootedAtomBounded L d N} :
-- imply
  ons_decRootedAtomExponent (ons_decForgetBoundedRoot root) = ons_decBoundedRootExponent root := by
-- proof
  apply StatMech.Onsager.ons_decForgetBoundedRoot_exponent root

/--
[ons_decForgetBoundedRoot_weight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_decForgetBoundedRoot_weight_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {N : ℕ}
  {d : ons_Dart L}
  {root : ons_DecRootedAtomBounded L d N} :
-- imply
  ons_decRootedAtomWeight L a b (ons_decForgetBoundedRoot root) = ons_decBoundedRootWeight L a b root := by
-- proof
  apply StatMech.Onsager.ons_decForgetBoundedRoot_weight L a b root

/--
[ons_decBoundedRootToUnbounded_bijective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_decBoundedRootToUnbounded_bijective_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {m : ons_DecEdge L →₀ ℕ} :
-- imply
  Function.Bijective (ons_decBoundedRootToUnbounded L d m) := by
-- proof
  apply StatMech.Onsager.ons_decBoundedRootToUnbounded_bijective L d m

/--
[ons_decFormalRootedLogCoeff_eq_boundedRootSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_decFormalRootedLogCoeff_eq_boundedRootSum_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {d : ons_Dart L}
  {m : ons_DecEdge L →₀ ℕ} :
-- imply
  ons_decFormalRootedLogCoeff L a b d m = -(∑ root : ons_DecRootedAtomBounded L d (ons_finsuppTotalDegree m), if ons_decBoundedRootExponent root = m then ons_decBoundedRootWeight L a b root / (ons_visitCount d root.2.1 : ℂ) else 0) := by
-- proof
  apply StatMech.Onsager.ons_decFormalRootedLogCoeff_eq_boundedRootSum L a b d m

/--
[ons_decFormalRootedLogCoeff_eq_zero_of_external_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_decFormalRootedLogCoeff_eq_zero_of_external_zero_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {d : ons_Dart L}
  {m : ons_DecEdge L →₀ ℕ}
-- given
  (hzero : m s(d, ons_dartRev L d) = 0) :
-- imply
  ons_decFormalRootedLogCoeff L a b d m = 0 := by
-- proof
  apply StatMech.Onsager.ons_decFormalRootedLogCoeff_eq_zero_of_external_zero L a b d m hzero

/--
[ons_decRootedExponentEquivUnboundedTuples_weight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_decRootedExponentEquivUnboundedTuples_weight_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {d : ons_Dart L}
  {m : ons_DecEdge L →₀ ℕ}
-- given
  (hk : 0 < m s(d, ons_dartRev L d))
  (root : {root : ons_DecRootedAtom L d // ons_decRootedAtomExponent root = m}) :
-- imply
  ons_decRootedAtomWeight L a b root.1 = ∏ i, ons_decFirstReturnAtomWeight L a b ((ons_decRootedExponentEquivUnboundedTuples L d m hk root).1 i) := by
-- proof
  apply StatMech.Onsager.ons_decRootedExponentEquivUnboundedTuples_weight L a b d m hk root

/--
[ons_decBoundedRootEquivBoundedTuples_weight_div](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_decBoundedRootEquivBoundedTuples_weight_div_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {d : ons_Dart L}
  {m : ons_DecEdge L →₀ ℕ}
-- given
  (hk : 0 < m s(d, ons_dartRev L d))
  (root : {root : ons_DecRootedAtomBounded L d (ons_finsuppTotalDegree m) // ons_decBoundedRootExponent root = m}) :
-- imply
  ons_decBoundedRootWeight L a b root.1 / (ons_visitCount d root.1.2.1 : ℂ) = (∏ i, ons_decBoundedAtomWeight L a b ((ons_decBoundedRootEquivBoundedTuples L d m hk root).1 i)) / (m s(d, ons_dartRev L d) : ℂ) := by
-- proof
  apply StatMech.Onsager.ons_decBoundedRootEquivBoundedTuples_weight_div L a b d m hk root

/--
[ons_decFormalRootedLogCoeff_eq_neg_coeff_pow_div](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_decFormalRootedLogCoeff_eq_neg_coeff_pow_div_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {d : ons_Dart L}
  {m : ons_DecEdge L →₀ ℕ}
-- given
  (hk : 0 < m s(d, ons_dartRev L d)) :
-- imply
  ons_decFormalRootedLogCoeff L a b d m = -(MvPowerSeries.coeff m (ons_decFormalFirstReturn L a b d ^ m s(d, ons_dartRev L d)) / (m s(d, ons_dartRev L d) : ℂ)) := by
-- proof
  apply StatMech.Onsager.ons_decFormalRootedLogCoeff_eq_neg_coeff_pow_div L a b d m hk

/--
[ons_decBoundedAtom_externalExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_decBoundedAtom_externalExponent_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {N : ℕ}
  {atom : ons_DecFirstReturnAtomBounded L d N} :
-- imply
  ons_decBoundedAtomExponent atom s(d, ons_dartRev L d) = 1 := by
-- proof
  apply StatMech.Onsager.ons_decBoundedAtom_externalExponent L d atom

/--
[ons_decFormalFirstReturn_coeff_pow_eq_zero_of_ne_external](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_decFormalFirstReturn_coeff_pow_eq_zero_of_ne_external_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {d : ons_Dart L}
  {m : ons_DecEdge L →₀ ℕ}
  {k : ℕ}
-- given
  (hne : k ≠ m s(d, ons_dartRev L d)) :
-- imply
  MvPowerSeries.coeff m (ons_decFormalFirstReturn L a b d ^ k) = 0 := by
-- proof
  apply StatMech.Onsager.ons_decFormalFirstReturn_coeff_pow_eq_zero_of_ne_external L a b d m k hne

/--
[ons_decFormalFirstReturn_neg_coeff_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_decFormalFirstReturn_neg_coeff_pow_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {d : ons_Dart L}
  {m : ons_DecEdge L →₀ ℕ}
  {k : ℕ} :
-- imply
  MvPowerSeries.coeff m ((-ons_decFormalFirstReturn L a b d) ^ k) = (-1 : ℂ) ^ k * MvPowerSeries.coeff m (ons_decFormalFirstReturn L a b d ^ k) := by
-- proof
  apply StatMech.Onsager.ons_decFormalFirstReturn_neg_coeff_pow L a b d m k

/--
[ons_decFormalFirstReturn_neg_hasSubst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_decFormalFirstReturn_neg_hasSubst_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {d : ons_Dart L} :
-- imply
  PowerSeries.HasSubst (-ons_decFormalFirstReturn L a b d) := by
-- proof
  apply StatMech.Onsager.ons_decFormalFirstReturn_neg_hasSubst L a b d

/--
[ons_decFormalRootedLogCoeff_eq_log_subst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_decFormalRootedLogCoeff_eq_log_subst_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {d : ons_Dart L}
  {m : ons_DecEdge L →₀ ℕ} :
-- imply
  ons_decFormalRootedLogCoeff L a b d m = MvPowerSeries.coeff m (PowerSeries.subst (-ons_decFormalFirstReturn L a b d) (PowerSeries.log ℂ)) := by
-- proof
  apply StatMech.Onsager.ons_decFormalRootedLogCoeff_eq_log_subst L a b d m

/--
[ons_decFormalRootedLog_eq_log_subst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_decFormalRootedLog_eq_log_subst_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {d : ons_Dart L} :
-- imply
  ons_decFormalRootedLog L a b d = PowerSeries.subst (-ons_decFormalFirstReturn L a b d) (PowerSeries.log ℂ) := by
-- proof
  apply StatMech.Onsager.ons_decFormalRootedLog_eq_log_subst L a b d

/--
[ons_powerSeries_deriv_deriv_log](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_powerSeries_deriv_deriv_log_eq :
-- imply
  PowerSeries.derivative ℂ (PowerSeries.derivative ℂ (PowerSeries.log ℂ)) = -((PowerSeries.derivative ℂ (PowerSeries.log ℂ)) ^ 2) := by
-- proof
  apply StatMech.Onsager.ons_powerSeries_deriv_deriv_log

/--
[ons_powerSeries_exp_log](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_powerSeries_exp_log_eq :
-- imply
  PowerSeries.subst (PowerSeries.log ℂ) (PowerSeries.exp ℂ) = 1 + PowerSeries.X := by
-- proof
  apply StatMech.Onsager.ons_powerSeries_exp_log

/--
[ons_decFormalRootedExp_eq_one_sub_firstReturn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_decFormalRootedExp_eq_one_sub_firstReturn_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {d : ons_Dart L} :
-- imply
  PowerSeries.subst (ons_decFormalRootedLog L a b d) (PowerSeries.exp ℂ) = 1 - ons_decFormalFirstReturn L a b d := by
-- proof
  apply StatMech.Onsager.ons_decFormalRootedExp_eq_one_sub_firstReturn L a b d

/--
[fin2_exp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma fin2_exp_eq
  {e : Fin 2 →₀ ℕ} :
-- imply
  Finsupp.single (0 : Fin 2) (e 0) + Finsupp.single (1 : Fin 2) (e 1) = e := by
-- proof
  apply StatMech.Onsager.DecFormalExpAdd.fin2_exp e

/--
[ex_coeff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ex_coeff_eq
  {e : Fin 2 →₀ ℕ} :
-- imply
  MvPowerSeries.coeff e (PowerSeries.subst (MvPowerSeries.X (0 : Fin 2)) (PowerSeries.exp ℂ)) = if e 1 = 0 then (1 : ℂ) / (e 0).factorial else 0 := by
-- proof
  apply StatMech.Onsager.DecFormalExpAdd.ex_coeff e

/--
[ey_coeff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ey_coeff_eq
  {e : Fin 2 →₀ ℕ} :
-- imply
  MvPowerSeries.coeff e (PowerSeries.subst (MvPowerSeries.X (1 : Fin 2)) (PowerSeries.exp ℂ)) = if e 0 = 0 then (1 : ℂ) / (e 1).factorial else 0 := by
-- proof
  apply StatMech.Onsager.DecFormalExpAdd.ey_coeff e

/--
[prod_coeff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma prod_coeff_eq
  {e : Fin 2 →₀ ℕ} :
-- imply
  MvPowerSeries.coeff e (PowerSeries.subst (MvPowerSeries.X (0 : Fin 2)) (PowerSeries.exp ℂ) * PowerSeries.subst (MvPowerSeries.X (1 : Fin 2)) (PowerSeries.exp ℂ)) = (1 : ℂ) / ((e 0).factorial * (e 1).factorial) := by
-- proof
  apply StatMech.Onsager.DecFormalExpAdd.prod_coeff e

/--
[add_coeff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma add_coeff_eq
  {e : Fin 2 →₀ ℕ} :
-- imply
  MvPowerSeries.coeff e (PowerSeries.subst (MvPowerSeries.X (0 : Fin 2) + MvPowerSeries.X (1 : Fin 2)) (PowerSeries.exp ℂ)) = (1 : ℂ) / ((e 0).factorial * (e 1).factorial) := by
-- proof
  apply StatMech.Onsager.DecFormalExpAdd.add_coeff e

/--
[biv_exp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma biv_exp_eq :
-- imply
  PowerSeries.subst (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) ℂ) (PowerSeries.exp ℂ) * PowerSeries.subst (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) ℂ) (PowerSeries.exp ℂ) = PowerSeries.subst ((MvPowerSeries.X (0 : Fin 2) + MvPowerSeries.X (1 : Fin 2)) : MvPowerSeries (Fin 2) ℂ) (PowerSeries.exp ℂ) := by
-- proof
  apply StatMech.Onsager.DecFormalExpAdd.biv_exp

/--
[ons_powerSeries_subst_exp_add_of_constantCoeff_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_powerSeries_subst_exp_add_of_constantCoeff_zero_eq
  {A B : MvPowerSeries τ ℂ}
-- given
  (hA : MvPowerSeries.constantCoeff A = 0)
  (hB : MvPowerSeries.constantCoeff B = 0) :
-- imply
  PowerSeries.subst A (PowerSeries.exp ℂ) * PowerSeries.subst B (PowerSeries.exp ℂ) = PowerSeries.subst (A + B) (PowerSeries.exp ℂ) := by
-- proof
  apply StatMech.Onsager.ons_powerSeries_subst_exp_add_of_constantCoeff_zero A B hA hB

/--
[ons_decFormalRootedLog_constantCoeff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_decFormalRootedLog_constantCoeff_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {d : ons_Dart L} :
-- imply
  MvPowerSeries.constantCoeff (ons_decFormalRootedLog L a b d) = 0 := by
-- proof
  apply StatMech.Onsager.ons_decFormalRootedLog_constantCoeff L a b d

/--
[ons_decFormalRoot_eq_avoidRoot_mul_one_sub_firstReturn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_decFormalRoot_eq_avoidRoot_mul_one_sub_firstReturn_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {d : ons_Dart L} :
-- imply
  ons_decFormalRoot L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b) = ons_decFormalAvoidRoot L a b d * (1 - ons_decFormalFirstReturn L a b d) := by
-- proof
  apply StatMech.Onsager.ons_decFormalRoot_eq_avoidRoot_mul_one_sub_firstReturn L a b d

/--
[ons_one_sub_decFormalFirstReturn_coeff_eq_zero_of_external_ge_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_one_sub_decFormalFirstReturn_coeff_eq_zero_of_external_ge_two_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {d : ons_Dart L}
  {m : ons_DecEdge L →₀ ℕ}
-- given
  (hmedge : 1 < m s(d, ons_dartRev L d)) :
-- imply
  MvPowerSeries.coeff m (1 - ons_decFormalFirstReturn L a b d) = 0 := by
-- proof
  apply StatMech.Onsager.ons_one_sub_decFormalFirstReturn_coeff_eq_zero_of_external_ge_two L a b d m hmedge

/--
[ons_decFormalRoot_coeff_eq_zero_of_external_ge_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean)
-/
@[path]
private lemma ons_decFormalRoot_coeff_eq_zero_of_external_ge_two_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {d : ons_Dart L}
  {m : ons_DecEdge L →₀ ℕ}
-- given
  (hmedge : 1 < m s(d, ons_dartRev L d)) :
-- imply
  MvPowerSeries.coeff m (ons_decFormalRoot L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) = 0 := by
-- proof
  apply StatMech.Onsager.ons_decFormalRoot_coeff_eq_zero_of_external_ge_two L a b d m hmedge


-- created on 2026-10-23
