import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.ShermanReroot.Part4
open StatMech StatMech.Onsager


/--
[ons_rotate_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanReroot.lean)
-/
@[path]
private lemma ons_rotate_apply_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  [NeZero n]
  {k j : Fin n}
  {v : Fin n → E} :
-- imply
  ons_rotate k v j = v (j + k) := by
-- proof
  apply StatMech.Onsager.ons_rotate_apply k j v

/--
[ons_rotate_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanReroot.lean)
-/
@[path]
private lemma ons_rotate_zero_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  [NeZero n]
  {k : Fin n}
  {v : Fin n → E} :
-- imply
  ons_rotate k v 0 = v k := by
-- proof
  apply StatMech.Onsager.ons_rotate_zero k v

/--
[ons_rotate_eq_iterate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanReroot.lean)
-/
@[path]
private lemma ons_rotate_eq_iterate_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  [NeZero n]
  {k : Fin n}
  {v : Fin n → E} :
-- imply
  ons_rotate k v = ons_cyclicShift^[k.val] v := by
-- proof
  apply StatMech.Onsager.ons_rotate_eq_iterate k v

/--
[ons_loopWeight_rotate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanReroot.lean)
-/
@[path]
private lemma ons_loopWeight_rotate_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  [NeZero n]
  {Lambda : Matrix E E ℂ}
  {k : Fin n}
  {v : Fin n → E} :
-- imply
  ons_loopWeight Lambda (ons_rotate k v) = ons_loopWeight Lambda v := by
-- proof
  apply StatMech.Onsager.ons_loopWeight_rotate Lambda k v

/--
[ons_visitCount_eq_card_filter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanReroot.lean)
-/
@[path]
private lemma ons_visitCount_eq_card_filter_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  [NeZero n]
  {e : E}
  {v : Fin n → E} :
-- imply
  ons_visitCount e v = (Finset.univ.filter fun k : Fin n => v k = e).card := by
-- proof
  apply StatMech.Onsager.ons_visitCount_eq_card_filter e v

/--
[ons_visitCount_pos_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanReroot.lean)
-/
@[path]
private lemma ons_visitCount_pos_iff_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  [NeZero n]
  {e : E}
  {v : Fin n → E} :
-- imply
  0 < ons_visitCount e v ↔ ∃ k, v k = e := by
-- proof
  apply StatMech.Onsager.ons_visitCount_pos_iff e v

/--
[ons_visitCount_rotate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanReroot.lean)
-/
@[path]
private lemma ons_visitCount_rotate_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  [NeZero n]
  {e : E}
  {k : Fin n}
  {v : Fin n → E} :
-- imply
  ons_visitCount e (ons_rotate k v) = ons_visitCount e v := by
-- proof
  apply StatMech.Onsager.ons_visitCount_rotate e k v

/--
[ons_avoids_rotate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanReroot.lean)
-/
@[path]
private lemma ons_avoids_rotate_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  [NeZero n]
  {r : E}
  {k : Fin n}
  {v : Fin n → E} :
-- imply
  (∀ j, ons_rotate k v j ≠ r) ↔ ∀ j, v j ≠ r := by
-- proof
  apply StatMech.Onsager.ons_avoids_rotate r k v

/--
[ons_loopSum_div_length_eq_rerooted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanReroot.lean)
-/
@[path]
private lemma ons_loopSum_div_length_eq_rerooted_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  [NeZero n]
  {Lambda : Matrix E E ℂ}
  {e r : E} :
-- imply
  (∑ v ∈ Finset.univ.filter (fun v : Fin n → E => (∃ k, v k = e) ∧ ∀ j, v j ≠ r), ons_loopWeight Lambda v) / (n : ℂ) = ∑ v ∈ Finset.univ.filter (fun v : Fin n → E => v 0 = e ∧ ∀ j, v j ≠ r), ons_loopWeight Lambda v / (ons_visitCount e v : ℂ) := by
-- proof
  apply StatMech.Onsager.ons_loopSum_div_length_eq_rerooted Lambda e r

/--
[ons_firstReturnFactors_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanReroot.lean)
-/
@[path]
private lemma ons_firstReturnFactors_length_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  [NeZero n]
  {e : E}
  {v : Fin n → E}
-- given
  (hroot : v 0 = e) :
-- imply
  (ons_firstReturnFactors e (List.ofFn v ++ [e])).length = ons_visitCount e v := by
-- proof
  apply StatMech.Onsager.ons_firstReturnFactors_length e v hroot


-- created on 2026-10-23
