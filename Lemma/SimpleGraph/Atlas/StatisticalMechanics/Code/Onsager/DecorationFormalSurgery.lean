import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Onsager.DecorationFormalSurgery
open StatMech StatMech.Onsager


/--
[ons_decLoopSetBothExponent_scalar_sum_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalSurgery.lean)
-/
@[path]
private lemma ons_decLoopSetBothExponent_scalar_sum_eq_zero_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {n : ℕ}
  [NeZero n]
  {d : ons_Dart L}
  {m : ons_DecEdge L →₀ ℕ} :
-- imply
  (∑ loop ∈ ons_decLoopSetBothExponent (n := n) L a b d m, ons_decLoopScalar L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b) loop) = 0 := by
-- proof
  apply StatMech.Onsager.ons_decLoopSetBothExponent_scalar_sum_eq_zero L a b d m

/--
[ons_decLoopScalar_sum_both_fixedExponent_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalSurgery.lean)
-/
@[path]
private lemma ons_decLoopScalar_sum_both_fixedExponent_eq_zero_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {n : ℕ}
  [NeZero n]
  {d : ons_Dart L}
  {m : ons_DecEdge L →₀ ℕ} :
-- imply
  (∑ loop ∈ ons_loopSetBoth (n := n) d (ons_dartRev L d), if ons_decLoopExponent L loop = m then ons_decLoopScalar L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b) loop else 0) = 0 := by
-- proof
  apply StatMech.Onsager.ons_decLoopScalar_sum_both_fixedExponent_eq_zero L a b d m

/--
[ons_decFixedExponentTerm_loopRev](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalSurgery.lean)
-/
@[path]
private lemma ons_decFixedExponentTerm_loopRev_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {n : ℕ}
  [NeZero n]
  {m : ons_DecEdge L →₀ ℕ}
  {loop : Fin n → ons_Dart L} :
-- imply
  (if ons_decLoopExponent L (ons_loopRev L loop) = m then ons_decLoopScalar L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b) (ons_loopRev L loop) else 0) = if ons_decLoopExponent L loop = m then ons_decLoopScalar L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b) loop else 0 := by
-- proof
  apply StatMech.Onsager.ons_decFixedExponentTerm_loopRev L a b m loop

/--
[ons_decLoopScalar_sum_one_orientation_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalSurgery.lean)
-/
@[path]
private lemma ons_decLoopScalar_sum_one_orientation_symm_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {n : ℕ}
  [NeZero n]
  {d : ons_Dart L}
  {m : ons_DecEdge L →₀ ℕ} :
-- imply
  (∑ loop ∈ Finset.univ.filter (fun loop : Fin n → ons_Dart L ↦ (∃ k, loop k = d) ∧ ¬ ∃ k, loop k = ons_dartRev L d), if ons_decLoopExponent L loop = m then ons_decLoopScalar L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b) loop else 0) = ∑ loop ∈ Finset.univ.filter (fun loop : Fin n → ons_Dart L ↦ (∃ k, loop k = ons_dartRev L d) ∧ ¬ ∃ k, loop k = d), if ons_decLoopExponent L loop = m then ons_decLoopScalar L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b) loop else 0 := by
-- proof
  apply StatMech.Onsager.ons_decLoopScalar_sum_one_orientation_symm L a b d m

/--
[ons_decLoopScalar_sum_fixedExponent_two_bucket](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalSurgery.lean)
-/
@[path]
private lemma ons_decLoopScalar_sum_fixedExponent_two_bucket_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {d : ons_Dart L}
  {r : ℕ}
  {m : ons_DecEdge L →₀ ℕ} :
-- imply
  (∑ loop : Fin (r + 1) → ons_Dart L, if ons_decLoopExponent L loop = m then ons_decLoopScalar L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b) loop else 0) = 2 * ons_decFormalFixedBucketE L a b d r m + ons_decFormalFixedBucketN L a b d r m := by
-- proof
  apply StatMech.Onsager.ons_decLoopScalar_sum_fixedExponent_two_bucket L a b d r m


-- created on 2026-10-23
