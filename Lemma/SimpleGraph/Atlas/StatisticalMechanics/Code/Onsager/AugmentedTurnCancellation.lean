import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.AugmentedTurnCancellation.Part5
open StatMech StatMech.Onsager


/--
[ons_turnProduct_surgery_sign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/AugmentedTurnCancellation.lean)
-/
@[path]
private lemma ons_turnProduct_surgery_sign_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  [NeZero n]
  {rev : E → E}
  {dir : E → Fin 4}
  {omega : ℂ}
  {e : E}
  {loop : Fin n → E}
-- given
  (hrev : Function.Involutive rev)
  (hdir : ∀ e, dir (rev e) = dir e + 2)
  (homega : omega ≠ 0)
  (hI : omega ^ 2 = Complex.I)
  (hloop : (∃ i, loop i = e) ∧ (∃ j, loop j = rev e)) :
-- imply
  (∏ k, ons_turnW omega (dir (ons_surgery e rev loop (k + 1))) (dir (ons_surgery e rev loop k))) = -∏ k, ons_turnW omega (dir (loop (k + 1))) (dir (loop k)) := by
-- proof
  apply StatMech.Onsager.ons_turnProduct_surgery_sign rev hrev dir hdir omega homega hI e loop hloop

/--
[ons_reversibleFactorProduct_surgery](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/AugmentedTurnCancellation.lean)
-/
@[path]
private lemma ons_reversibleFactorProduct_surgery_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  [NeZero n]
  {rev : E → E}
  {dir : E → Fin 4}
  {q : E → E → ℂ}
  {e : E}
  {loop : Fin n → E}
-- given
  (hrev : Function.Involutive rev)
  (hdir : ∀ e, dir (rev e) = dir e + 2)
  (hq : ∀ x y, q (rev y) (rev x) = q x y)
  (hloop : (∃ i, loop i = e) ∧ (∃ j, loop j = rev e)) :
-- imply
  (∏ k, q (ons_surgery e rev loop k) (ons_surgery e rev loop (k + 1))) = ∏ k, q (loop k) (loop (k + 1)) := by
-- proof
  apply StatMech.Onsager.ons_reversibleFactorProduct_surgery rev hrev dir hdir q hq e loop hloop

/--
[ons_reversibleTurnMatrix_surgery_sign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/AugmentedTurnCancellation.lean)
-/
@[path]
private lemma ons_reversibleTurnMatrix_surgery_sign_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  [NeZero n]
  {rev : E → E}
  {dir : E → Fin 4}
  {omega : ℂ}
  {q : E → E → ℂ}
  {e : E}
  {loop : Fin n → E}
-- given
  (hrev : Function.Involutive rev)
  (hdir : ∀ e, dir (rev e) = dir e + 2)
  (homega : omega ≠ 0)
  (hI : omega ^ 2 = Complex.I)
  (hq : ∀ x y, q (rev y) (rev x) = q x y)
  (hloop : (∃ i, loop i = e) ∧ (∃ j, loop j = rev e)) :
-- imply
  ons_loopWeight (ons_reversibleTurnMatrix dir omega q) (ons_surgery e rev loop) = -ons_loopWeight (ons_reversibleTurnMatrix dir omega q) loop := by
-- proof
  apply StatMech.Onsager.ons_reversibleTurnMatrix_surgery_sign rev hrev dir hdir omega homega hI q hq e loop hloop

/--
[ons_reversibleTurnMatrix_lemma5](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/AugmentedTurnCancellation.lean)
-/
@[path]
private lemma ons_reversibleTurnMatrix_lemma5_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  [NeZero n]
  {rev : E → E}
  {dir : E → Fin 4}
  {omega : ℂ}
  {q : E → E → ℂ}
  {e : E}
-- given
  (hrev : Function.Involutive rev)
  (hdir : ∀ e, dir (rev e) = dir e + 2)
  (homega : omega ≠ 0)
  (hI : omega ^ 2 = Complex.I)
  (hq : ∀ x y, q (rev y) (rev x) = q x y)
  (hrne : rev e ≠ e) :
-- imply
  ∑ loop ∈ ons_loopSetBoth (n := n) e (rev e), ons_loopWeight (ons_reversibleTurnMatrix dir omega q) loop = 0 := by
-- proof
  apply StatMech.Onsager.ons_reversibleTurnMatrix_lemma5 rev hrev dir hdir omega homega hI q hq e hrne

/--
[ons_invariantStateProduct_surgery](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/AugmentedTurnCancellation.lean)
-/
@[path]
private lemma ons_invariantStateProduct_surgery_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  [NeZero n]
  {rev : E → E}
  {weight : E → ℂ}
  {e : E}
  {loop : Fin n → E}
-- given
  (hrev : Function.Involutive rev)
  (hweight : ∀ x, weight (rev x) = weight x)
  (hloop : (∃ i, loop i = e) ∧ (∃ j, loop j = rev e)) :
-- imply
  (∏ k, weight (ons_surgery e rev loop k)) = ∏ k, weight (loop k) := by
-- proof
  apply StatMech.Onsager.ons_invariantStateProduct_surgery rev hrev weight hweight e loop hloop

/--
[ons_loopWeight_stateWeightedReversibleTurnMatrix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/AugmentedTurnCancellation.lean)
-/
@[path]
private lemma ons_loopWeight_stateWeightedReversibleTurnMatrix_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  [NeZero n]
  {dir : E → Fin 4}
  {omega : ℂ}
  {rowWeight colWeight : E → ℂ}
  {q : E → E → ℂ}
  {loop : Fin n → E} :
-- imply
  ons_loopWeight (ons_stateWeightedReversibleTurnMatrix dir omega rowWeight colWeight q) loop = (∏ k, rowWeight (loop k) * colWeight (loop k)) * (∏ k, q (loop k) (loop (k + 1))) * ∏ k, ons_turnW omega (dir (loop (k + 1))) (dir (loop k)) := by
-- proof
  apply StatMech.Onsager.ons_loopWeight_stateWeightedReversibleTurnMatrix dir omega rowWeight colWeight q loop

/--
[ons_stateWeightedReversibleTurnMatrix_surgery_sign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/AugmentedTurnCancellation.lean)
-/
@[path]
private lemma ons_stateWeightedReversibleTurnMatrix_surgery_sign_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  [NeZero n]
  {rev : E → E}
  {dir : E → Fin 4}
  {omega : ℂ}
  {rowWeight colWeight : E → ℂ}
  {q : E → E → ℂ}
  {e : E}
  {loop : Fin n → E}
-- given
  (hrev : Function.Involutive rev)
  (hdir : ∀ e, dir (rev e) = dir e + 2)
  (homega : omega ≠ 0)
  (hI : omega ^ 2 = Complex.I)
  (hweight : ∀ x, rowWeight (rev x) * colWeight (rev x) = rowWeight x * colWeight x)
  (hq : ∀ x y, q (rev y) (rev x) = q x y)
  (hloop : (∃ i, loop i = e) ∧ (∃ j, loop j = rev e)) :
-- imply
  ons_loopWeight (ons_stateWeightedReversibleTurnMatrix dir omega rowWeight colWeight q) (ons_surgery e rev loop) = -ons_loopWeight (ons_stateWeightedReversibleTurnMatrix dir omega rowWeight colWeight q) loop := by
-- proof
  apply StatMech.Onsager.ons_stateWeightedReversibleTurnMatrix_surgery_sign rev hrev dir hdir omega homega hI rowWeight colWeight hweight q hq e loop hloop

/--
[ons_stateWeightedReversibleTurnMatrix_lemma5](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/AugmentedTurnCancellation.lean)
-/
@[path]
private lemma ons_stateWeightedReversibleTurnMatrix_lemma5_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  [NeZero n]
  {rev : E → E}
  {dir : E → Fin 4}
  {omega : ℂ}
  {rowWeight colWeight : E → ℂ}
  {q : E → E → ℂ}
  {e : E}
-- given
  (hrev : Function.Involutive rev)
  (hdir : ∀ e, dir (rev e) = dir e + 2)
  (homega : omega ≠ 0)
  (hI : omega ^ 2 = Complex.I)
  (hweight : ∀ x, rowWeight (rev x) * colWeight (rev x) = rowWeight x * colWeight x)
  (hq : ∀ x y, q (rev y) (rev x) = q x y)
  (hrne : rev e ≠ e) :
-- imply
  ∑ loop ∈ ons_loopSetBoth (n := n) e (rev e), ons_loopWeight (ons_stateWeightedReversibleTurnMatrix dir omega rowWeight colWeight q) loop = 0 := by
-- proof
  apply StatMech.Onsager.ons_stateWeightedReversibleTurnMatrix_lemma5 rev hrev dir hdir omega homega hI rowWeight colWeight hweight q hq e hrne

/--
[ons_cyclicTurnProduct_omega_inv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/AugmentedTurnCancellation.lean)
-/
@[path]
private lemma ons_cyclicTurnProduct_omega_inv_eq
  {n : ℕ}
  [NeZero n]
  {omega : ℂ}
  {d : Fin n → Fin 4}
-- given
  (homega : omega ≠ 0)
  (hI : omega ^ 2 = Complex.I) :
-- imply
  (∏ k, ons_turnW omega⁻¹ (d (k + 1)) (d k)) = ∏ k, ons_turnW omega (d (k + 1)) (d k) := by
-- proof
  apply StatMech.Onsager.ons_cyclicTurnProduct_omega_inv omega homega hI d

/--
[ons_involutiveLoopRev_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/AugmentedTurnCancellation.lean)
-/
@[path]
private lemma ons_involutiveLoopRev_involutive_eq
  {n : ℕ}
  [NeZero n]
  {rev : E → E}
  {loop : Fin n → E}
-- given
  (hrev : Function.Involutive rev) :
-- imply
  ons_involutiveLoopRev rev (ons_involutiveLoopRev rev loop) = loop := by
-- proof
  apply StatMech.Onsager.ons_involutiveLoopRev_involutive rev hrev loop

/--
[ons_visits_involutiveLoopRev](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/AugmentedTurnCancellation.lean)
-/
@[path]
private lemma ons_visits_involutiveLoopRev_eq
  {n : ℕ}
  [NeZero n]
  {rev : E → E}
  {loop : Fin n → E}
  {e : E}
-- given
  (hrev : Function.Involutive rev) :
-- imply
  (∃ i, ons_involutiveLoopRev rev loop i = e) ↔ ∃ i, loop i = rev e := by
-- proof
  apply StatMech.Onsager.ons_visits_involutiveLoopRev rev hrev loop e

/--
[ons_loopWeight_stateWeightedReversibleTurnMatrix_loopRev](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/AugmentedTurnCancellation.lean)
-/
@[path]
private lemma ons_loopWeight_stateWeightedReversibleTurnMatrix_loopRev_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  [NeZero n]
  {rev : E → E}
  {dir : E → Fin 4}
  {omega : ℂ}
  {rowWeight colWeight : E → ℂ}
  {q : E → E → ℂ}
  {loop : Fin n → E}
-- given
  (hdir : ∀ e, dir (rev e) = dir e + 2)
  (homega : omega ≠ 0)
  (hI : omega ^ 2 = Complex.I)
  (hweight : ∀ x, rowWeight (rev x) * colWeight (rev x) = rowWeight x * colWeight x)
  (hq : ∀ x y, q (rev y) (rev x) = q x y) :
-- imply
  ons_loopWeight (ons_stateWeightedReversibleTurnMatrix dir omega rowWeight colWeight q) (ons_involutiveLoopRev rev loop) = ons_loopWeight (ons_stateWeightedReversibleTurnMatrix dir omega rowWeight colWeight q) loop := by
-- proof
  apply StatMech.Onsager.ons_loopWeight_stateWeightedReversibleTurnMatrix_loopRev rev dir hdir omega homega hI rowWeight colWeight hweight q hq loop

/--
[ons_mask_stateWeightedReversibleTurnMatrix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/AugmentedTurnCancellation.lean)
-/
@[path]
private lemma ons_mask_stateWeightedReversibleTurnMatrix_eq
  [Fintype E]
  [DecidableEq E]
  {forbidden : Finset E}
  {dir : E → Fin 4}
  {omega : ℂ}
  {rowWeight colWeight : E → ℂ}
  {q : E → E → ℂ} :
-- imply
  ons_maskMatrix forbidden (ons_stateWeightedReversibleTurnMatrix dir omega rowWeight colWeight q) = ons_stateWeightedReversibleTurnMatrix dir omega rowWeight colWeight (ons_maskedReversibleFactor forbidden q) := by
-- proof
  apply StatMech.Onsager.ons_mask_stateWeightedReversibleTurnMatrix forbidden dir omega rowWeight colWeight q

/--
[ons_maskedReversibleFactor_rev](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/AugmentedTurnCancellation.lean)
-/
@[path]
private lemma ons_maskedReversibleFactor_rev_eq
  [DecidableEq E]
  {rev : E → E}
  {forbidden : Finset E}
  {q : E → E → ℂ}
  {x y : E}
-- given
  (hforbidden : ∀ x, rev x ∈ forbidden ↔ x ∈ forbidden)
  (hq : ∀ x y, q (rev y) (rev x) = q x y) :
-- imply
  ons_maskedReversibleFactor forbidden q (rev y) (rev x) = ons_maskedReversibleFactor forbidden q x y := by
-- proof
  apply StatMech.Onsager.ons_maskedReversibleFactor_rev rev forbidden hforbidden q hq x y


-- created on 2026-10-23
