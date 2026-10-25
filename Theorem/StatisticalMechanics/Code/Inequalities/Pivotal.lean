/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Pivotal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2
import Def.StatisticalMechanics.Code.Inequalities.Pivotal


namespace StatMech

open ConfigSpace Function

variable {E : Type*} [DecidableEq E]


@[simp] lemma setOpen_self (e : E) (ω : ConfigSpace E) : setOpen e ω e = true :=
  Function.update_self _ _ _

@[simp] lemma setClosed_self (e : E) (ω : ConfigSpace E) : setClosed e ω e = false :=
  Function.update_self _ _ _

lemma setOpen_of_ne {e e' : E} (h : e' ≠ e) (ω : ConfigSpace E) :
    setOpen e ω e' = ω e' := Function.update_of_ne h _ _

lemma setClosed_of_ne {e e' : E} (h : e' ≠ e) (ω : ConfigSpace E) :
    setClosed e ω e' = ω e' := Function.update_of_ne h _ _


lemma setClosed_le_setOpen (e : E) (ω : ConfigSpace E) :
    setClosed e ω ≤ setOpen e ω := by
  unfold setClosed setOpen
  rw [update_le_update_iff']
  decide


lemma setOpen_congr {e : E} {ω ω' : ConfigSpace E}
    (h : ∀ e', e' ≠ e → ω e' = ω' e') : setOpen e ω = setOpen e ω' := by
  funext e'
  by_cases he : e' = e
  · subst he; simp
  · rw [setOpen_of_ne he, setOpen_of_ne he, h e' he]


lemma setClosed_congr {e : E} {ω ω' : ConfigSpace E}
    (h : ∀ e', e' ≠ e → ω e' = ω' e') : setClosed e ω = setClosed e ω' := by
  funext e'
  by_cases he : e' = e
  · subst he; simp
  · rw [setClosed_of_ne he, setClosed_of_ne he, h e' he]

@[simp] lemma setOpen_setClosed (e : E) (ω : ConfigSpace E) :
    setOpen e (setClosed e ω) = setOpen e ω := by
  unfold setOpen setClosed; rw [Function.update_idem]

@[simp] lemma setClosed_setOpen (e : E) (ω : ConfigSpace E) :
    setClosed e (setOpen e ω) = setClosed e ω := by
  unfold setOpen setClosed; rw [Function.update_idem]

@[simp] lemma setOpen_setOpen (e : E) (ω : ConfigSpace E) :
    setOpen e (setOpen e ω) = setOpen e ω := by
  unfold setOpen; rw [Function.update_idem]

@[simp] lemma setClosed_setClosed (e : E) (ω : ConfigSpace E) :
    setClosed e (setClosed e ω) = setClosed e ω := by
  unfold setClosed; rw [Function.update_idem]


end StatMech
