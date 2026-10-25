import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Onsager.ShermanLemma5.Part7
open StatMech StatMech.Onsager


/--
[ons_sum_zero_of_sign_involution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma5.lean)
-/
@[path]
private lemma ons_sum_zero_of_sign_involution_eq
  {E}
  [Fintype E]
  [DecidableEq E]
  {Λ : Matrix E E ℂ}
  {n : ℕ}
  [NeZero n]
  {S : Finset (Fin n → E)}
  {g : (Fin n → E) → (Fin n → E)}
-- given
  (hmaps : ∀ v ∈ S, g v ∈ S)
  (hsign : ∀ v ∈ S, ons_loopWeight Λ (g v) = - ons_loopWeight Λ v)
  (hinv : ∀ v ∈ S, g (g v) = v)
  (hne : ∀ v ∈ S, g v ≠ v) :
-- imply
  ∑ v ∈ S, ons_loopWeight Λ v = 0 := by
-- proof
  apply StatMech.Onsager.ons_sum_zero_of_sign_involution Λ S g hmaps hsign hinv hne

/--
[ons_mem_loopSetBoth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma5.lean)
-/
@[path]
private lemma ons_mem_loopSetBoth_eq
  {E}
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {a b : E}
  {v : Fin n → E} :
-- imply
  v ∈ ons_loopSetBoth (n := n) a b ↔ (∃ i, v i = a) ∧ (∃ j, v j = b) := by
-- proof
  apply StatMech.Onsager.ons_mem_loopSetBoth a b v

/--
[ons_lemma5_of_involution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma5.lean)
-/
@[path]
private lemma ons_lemma5_of_involution_eq
  {E}
  [Fintype E]
  [DecidableEq E]
  {Λ : Matrix E E ℂ}
  {n : ℕ}
  [NeZero n]
  {e : E}
  {rev : E → E}
  {g : (Fin n → E) → (Fin n → E)}
-- given
  (hmaps : ∀ v ∈ ons_loopSetBoth (n := n) e (rev e), g v ∈ ons_loopSetBoth (n := n) e (rev e))
  (hsign : ∀ v ∈ ons_loopSetBoth (n := n) e (rev e), ons_loopWeight Λ (g v) = - ons_loopWeight Λ v)
  (hinv : ∀ v ∈ ons_loopSetBoth (n := n) e (rev e), g (g v) = v)
  (hne : ∀ v ∈ ons_loopSetBoth (n := n) e (rev e), g v ≠ v) :
-- imply
  ∑ v ∈ ons_loopSetBoth (n := n) e (rev e), ons_loopWeight Λ v = 0 := by
-- proof
  apply StatMech.Onsager.ons_lemma5_of_involution Λ e rev g hmaps hsign hinv hne

/--
[ons_mir_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma5.lean)
-/
@[path]
private lemma ons_mir_val_eq
  {n : ℕ}
  [NeZero n]
  {l m k : Fin n}
-- given
  (hlk : l ≤ k)
  (hkm : k ≤ m) :
-- imply
  (ons_mir l m k).val = l.val + m.val - k.val := by
-- proof
  apply StatMech.Onsager.ons_mir_val hlk hkm

/--
[ons_mir_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma5.lean)
-/
@[path]
private lemma ons_mir_mem_eq
  {n : ℕ}
  [NeZero n]
  {l m k : Fin n}
-- given
  (hlk : l ≤ k)
  (hkm : k ≤ m) :
-- imply
  l ≤ ons_mir l m k ∧ ons_mir l m k ≤ m := by
-- proof
  apply StatMech.Onsager.ons_mir_mem hlk hkm

/--
[ons_mir_mir](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma5.lean)
-/
@[path]
private lemma ons_mir_mir_eq
  {n : ℕ}
  [NeZero n]
  {l m k : Fin n}
-- given
  (hlk : l ≤ k)
  (hkm : k ≤ m) :
-- imply
  ons_mir l m (ons_mir l m k) = k := by
-- proof
  apply StatMech.Onsager.ons_mir_mir hlk hkm

/--
[ons_mir_l](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma5.lean)
-/
@[path]
private lemma ons_mir_l_eq
  {n : ℕ}
  [NeZero n]
  {l m : Fin n}
-- given
  (hlm : l ≤ m) :
-- imply
  ons_mir l m l = m := by
-- proof
  apply StatMech.Onsager.ons_mir_l hlm

/--
[ons_mir_m](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma5.lean)
-/
@[path]
private lemma ons_mir_m_eq
  {n : ℕ}
  [NeZero n]
  {l m : Fin n}
-- given
  (hlm : l ≤ m) :
-- imply
  ons_mir l m m = l := by
-- proof
  apply StatMech.Onsager.ons_mir_m hlm

/--
[ons_revSeg_outside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma5.lean)
-/
@[path]
private lemma ons_revSeg_outside_eq
  {E}
  {n : ℕ}
  [NeZero n]
  {rev : E → E}
  {l m : Fin n}
  {v : Fin n → E}
  {k : Fin n}
-- given
  (h : ¬ (l ≤ k ∧ k ≤ m)) :
-- imply
  ons_revSeg rev l m v k = v k := by
-- proof
  apply StatMech.Onsager.ons_revSeg_outside rev v h

/--
[ons_revSeg_inside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma5.lean)
-/
@[path]
private lemma ons_revSeg_inside_eq
  {E}
  {n : ℕ}
  [NeZero n]
  {rev : E → E}
  {l m : Fin n}
  {v : Fin n → E}
  {k : Fin n}
-- given
  (hlk : l ≤ k)
  (hkm : k ≤ m) :
-- imply
  ons_revSeg rev l m v k = rev (v (ons_mir l m k)) := by
-- proof
  apply StatMech.Onsager.ons_revSeg_inside rev v hlk hkm

/--
[ons_revSeg_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma5.lean)
-/
@[path]
private lemma ons_revSeg_involutive_eq
  {E}
  {n : ℕ}
  [NeZero n]
  {rev : E → E}
  {l m : Fin n}
  {v : Fin n → E}
-- given
  (hrev : Function.Involutive rev) :
-- imply
  ons_revSeg rev l m (ons_revSeg rev l m v) = v := by
-- proof
  apply StatMech.Onsager.ons_revSeg_involutive hrev v

/--
[ons_mem_hitSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma5.lean)
-/
@[path]
private lemma ons_mem_hitSet_eq
  {E}
  [DecidableEq E]
  {n : ℕ}
  {e : E}
  {rev : E → E}
  {v : Fin n → E}
  {k : Fin n} :
-- imply
  k ∈ ons_hitSet e rev v ↔ v k = e ∨ v k = rev e := by
-- proof
  apply StatMech.Onsager.ons_mem_hitSet e rev v k

/--
[ons_mem_mSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma5.lean)
-/
@[path]
private lemma ons_mem_mSet_eq
  {E}
  [DecidableEq E]
  {n : ℕ}
  [NeZero n]
  {e : E}
  {rev : E → E}
  {v : Fin n → E}
  {j : Fin n} :
-- imply
  j ∈ ons_mSet e rev v ↔ v j = rev (v (ons_l e rev v)) := by
-- proof
  apply StatMech.Onsager.ons_mem_mSet e rev v j

/--
[ons_hitSet_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma5.lean)
-/
@[path]
private lemma ons_hitSet_nonempty_eq
  {E}
  [DecidableEq E]
  {n : ℕ}
  [NeZero n]
  {e : E}
  {rev : E → E}
  {v : Fin n → E}
-- given
  (h : (∃ i, v i = e) ∧ (∃ j, v j = rev e)) :
-- imply
  (ons_hitSet e rev v).Nonempty := by
-- proof
  apply StatMech.Onsager.ons_hitSet_nonempty h

/--
[ons_l_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma5.lean)
-/
@[path]
private lemma ons_l_eq_eq
  {E}
  [DecidableEq E]
  {n : ℕ}
  [NeZero n]
  {e : E}
  {rev : E → E}
  {v : Fin n → E}
-- given
  (h : (∃ i, v i = e) ∧ (∃ j, v j = rev e)) :
-- imply
  ons_l e rev v = (ons_hitSet e rev v).min' (ons_hitSet_nonempty h) := by
-- proof
  apply StatMech.Onsager.ons_l_eq h

/--
[ons_v_l_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma5.lean)
-/
@[path]
private lemma ons_v_l_mem_eq
  {E}
  [DecidableEq E]
  {n : ℕ}
  [NeZero n]
  {e : E}
  {rev : E → E}
  {v : Fin n → E}
-- given
  (h : (∃ i, v i = e) ∧ (∃ j, v j = rev e)) :
-- imply
  v (ons_l e rev v) = e ∨ v (ons_l e rev v) = rev e := by
-- proof
  apply StatMech.Onsager.ons_v_l_mem h

/--
[ons_mSet_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma5.lean)
-/
@[path]
private lemma ons_mSet_nonempty_eq
  {E}
  [DecidableEq E]
  {n : ℕ}
  [NeZero n]
  {e : E}
  {rev : E → E}
  {v : Fin n → E}
-- given
  (hrev : Function.Involutive rev)
  (h : (∃ i, v i = e) ∧ (∃ j, v j = rev e)) :
-- imply
  (ons_mSet e rev v).Nonempty := by
-- proof
  apply StatMech.Onsager.ons_mSet_nonempty hrev h

/--
[ons_m_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma5.lean)
-/
@[path]
private lemma ons_m_eq_eq
  {E}
  [DecidableEq E]
  {n : ℕ}
  [NeZero n]
  {e : E}
  {rev : E → E}
  {v : Fin n → E}
-- given
  (hrev : Function.Involutive rev)
  (h : (∃ i, v i = e) ∧ (∃ j, v j = rev e)) :
-- imply
  ons_m e rev v = (ons_mSet e rev v).max' (ons_mSet_nonempty hrev h) := by
-- proof
  apply StatMech.Onsager.ons_m_eq hrev h

/--
[ons_v_m](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma5.lean)
-/
@[path]
private lemma ons_v_m_eq
  {E}
  [DecidableEq E]
  {n : ℕ}
  [NeZero n]
  {e : E}
  {rev : E → E}
  {v : Fin n → E}
-- given
  (hrev : Function.Involutive rev)
  (h : (∃ i, v i = e) ∧ (∃ j, v j = rev e)) :
-- imply
  v (ons_m e rev v) = rev (v (ons_l e rev v)) := by
-- proof
  apply StatMech.Onsager.ons_v_m hrev h

/--
[ons_l_le_m](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma5.lean)
-/
@[path]
private lemma ons_l_le_m_eq
  {E}
  [DecidableEq E]
  {n : ℕ}
  [NeZero n]
  {e : E}
  {rev : E → E}
  {v : Fin n → E}
-- given
  (hrev : Function.Involutive rev)
  (h : (∃ i, v i = e) ∧ (∃ j, v j = rev e)) :
-- imply
  ons_l e rev v ≤ ons_m e rev v := by
-- proof
  apply StatMech.Onsager.ons_l_le_m hrev h

/--
[ons_surgery_eq_revSeg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma5.lean)
-/
@[path]
private lemma ons_surgery_eq_revSeg_eq
  {E}
  [DecidableEq E]
  {n : ℕ}
  [NeZero n]
  {e : E}
  {rev : E → E}
  {v : Fin n → E}
-- given
  (h : (∃ i, v i = e) ∧ (∃ j, v j = rev e)) :
-- imply
  ons_surgery e rev v = ons_revSeg rev (ons_l e rev v) (ons_m e rev v) v := by
-- proof
  apply StatMech.Onsager.ons_surgery_eq_revSeg h

/--
[ons_surgery_hits_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma5.lean)
-/
@[path]
private lemma ons_surgery_hits_iff_eq
  {E}
  [DecidableEq E]
  {n : ℕ}
  [NeZero n]
  {e : E}
  {rev : E → E}
  {S : Finset E}
  {v : Fin n → E}
-- given
  (hS : ∀ x, rev x ∈ S ↔ x ∈ S)
  (h : (∃ i, v i = e) ∧ (∃ j, v j = rev e)) :
-- imply
  (∃ k, ons_surgery e rev v k ∈ S) ↔ ∃ k, v k ∈ S := by
-- proof
  apply StatMech.Onsager.ons_surgery_hits_iff S hS h

/--
[ons_surgery_l](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma5.lean)
-/
@[path]
private lemma ons_surgery_l_eq
  {E}
  [DecidableEq E]
  {n : ℕ}
  [NeZero n]
  {e : E}
  {rev : E → E}
  {v : Fin n → E}
-- given
  (hrev : Function.Involutive rev)
  (h : (∃ i, v i = e) ∧ (∃ j, v j = rev e)) :
-- imply
  ons_surgery e rev v (ons_l e rev v) = v (ons_l e rev v) := by
-- proof
  apply StatMech.Onsager.ons_surgery_l hrev h

/--
[ons_surgery_m](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma5.lean)
-/
@[path]
private lemma ons_surgery_m_eq
  {E}
  [DecidableEq E]
  {n : ℕ}
  [NeZero n]
  {e : E}
  {rev : E → E}
  {v : Fin n → E}
-- given
  (hrev : Function.Involutive rev)
  (h : (∃ i, v i = e) ∧ (∃ j, v j = rev e)) :
-- imply
  ons_surgery e rev v (ons_m e rev v) = v (ons_m e rev v) := by
-- proof
  apply StatMech.Onsager.ons_surgery_m hrev h

/--
[ons_surgery_visitsBoth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma5.lean)
-/
@[path]
private lemma ons_surgery_visitsBoth_eq
  {E}
  [DecidableEq E]
  {n : ℕ}
  [NeZero n]
  {e : E}
  {rev : E → E}
  {v : Fin n → E}
-- given
  (hrev : Function.Involutive rev)
  (hrne : rev e ≠ e)
  (h : (∃ i, v i = e) ∧ (∃ j, v j = rev e)) :
-- imply
  (∃ i, ons_surgery e rev v i = e) ∧ (∃ j, ons_surgery e rev v j = rev e) := by
-- proof
  apply StatMech.Onsager.ons_surgery_visitsBoth hrev hrne h

/--
[ons_l_surgery](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma5.lean)
-/
@[path]
private lemma ons_l_surgery_eq
  {E}
  [DecidableEq E]
  {n : ℕ}
  [NeZero n]
  {e : E}
  {rev : E → E}
  {v : Fin n → E}
-- given
  (hrev : Function.Involutive rev)
  (hrne : rev e ≠ e)
  (h : (∃ i, v i = e) ∧ (∃ j, v j = rev e)) :
-- imply
  ons_l e rev (ons_surgery e rev v) = ons_l e rev v := by
-- proof
  apply StatMech.Onsager.ons_l_surgery hrev hrne h

/--
[ons_m_surgery](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma5.lean)
-/
@[path]
private lemma ons_m_surgery_eq
  {E}
  [DecidableEq E]
  {n : ℕ}
  [NeZero n]
  {e : E}
  {rev : E → E}
  {v : Fin n → E}
-- given
  (hrev : Function.Involutive rev)
  (hrne : rev e ≠ e)
  (h : (∃ i, v i = e) ∧ (∃ j, v j = rev e)) :
-- imply
  ons_m e rev (ons_surgery e rev v) = ons_m e rev v := by
-- proof
  apply StatMech.Onsager.ons_m_surgery hrev hrne h

/--
[ons_surgery_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma5.lean)
-/
@[path]
private lemma ons_surgery_involutive_eq
  {E}
  [DecidableEq E]
  {n : ℕ}
  [NeZero n]
  {e : E}
  {rev : E → E}
  {v : Fin n → E}
-- given
  (hrev : Function.Involutive rev)
  (hrne : rev e ≠ e)
  (h : (∃ i, v i = e) ∧ (∃ j, v j = rev e)) :
-- imply
  ons_surgery e rev (ons_surgery e rev v) = v := by
-- proof
  apply StatMech.Onsager.ons_surgery_involutive hrev hrne h

/--
[ons_sum_zero_of_sign_involution'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma5.lean)
-/
@[path]
private lemma ons_sum_zero_of_sign_involution'_eq
  {E}
  [Fintype E]
  [DecidableEq E]
  {Λ : Matrix E E ℂ}
  {n : ℕ}
  [NeZero n]
  {S : Finset (Fin n → E)}
  {g : (Fin n → E) → (Fin n → E)}
-- given
  (hmaps : ∀ v ∈ S, g v ∈ S)
  (hsign : ∀ v ∈ S, ons_loopWeight Λ (g v) = - ons_loopWeight Λ v)
  (hinv : ∀ v ∈ S, g (g v) = v) :
-- imply
  ∑ v ∈ S, ons_loopWeight Λ v = 0 := by
-- proof
  apply StatMech.Onsager.ons_sum_zero_of_sign_involution' Λ S g hmaps hsign hinv

/--
[ons_lemma5](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma5.lean)
-/
@[path]
private lemma ons_lemma5_eq
  {E}
  [Fintype E]
  [DecidableEq E]
  {Λ : Matrix E E ℂ}
  {n : ℕ}
  [NeZero n]
  {e : E}
  {rev : E → E}
-- given
  (hrev : Function.Involutive rev)
  (hrne : rev e ≠ e)
  (hsign : ∀ v ∈ ons_loopSetBoth (n := n) e (rev e), ons_loopWeight Λ (ons_surgery e rev v) = - ons_loopWeight Λ v) :
-- imply
  ∑ v ∈ ons_loopSetBoth (n := n) e (rev e), ons_loopWeight Λ v = 0 := by
-- proof
  apply StatMech.Onsager.ons_lemma5 Λ e rev hrev hrne hsign


-- created on 2026-10-23
