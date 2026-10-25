/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FluxEdgeCopyBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.Switching.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.RandomCurrent.Part10
import Theorem.StatisticalMechanics.Code.Sharpness.CurrentRep.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.TwoReplica.Part3
import Def.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge
open Finset BigOperators
open scoped symmDiff Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000


namespace StatMech

namespace Sharpness

namespace FluxEdgeCopy

variable {E : Type*} [Fintype E] [DecidableEq E] {β : E → Type*}
  [∀ e, Fintype (β e)] [∀ e, DecidableEq (β e)]


@[simp] theorem sigmaFinsetEquivPi_apply_card (S : Finset (Σ e : E, β e)) (e : E) :
    #(sigmaFinsetEquivPi S e) = #(S.filter (fun i : Σ e, β e => i.1 = e)) := by
  
  rw [show sigmaFinsetEquivPi S e
        = (univ : Finset (β e)).filter (fun b => (⟨e, b⟩ : Σ e, β e) ∈ S) from rfl]
  
  apply Finset.card_bij (fun b _ => (⟨e, b⟩ : Σ e, β e))
  · intro b hb
    simp only [mem_filter, mem_univ, true_and] at hb
    simp only [mem_filter, hb, true_and]
  · intro b₁ _ b₂ _ h
    simpa using h
  · intro i hi
    simp only [mem_filter] at hi
    obtain ⟨hS, he⟩ := hi
    subst he
    refine ⟨i.2, ?_, ?_⟩
    · simp only [mem_filter, mem_univ, true_and]; exact hS
    · rfl


theorem pi_card_profile_count (k : E → ℕ) :
    #(univ.filter (fun f : Π e : E, Finset (β e) => (fun e => #(f e)) = k))
      = ∏ e : E, (Fintype.card (β e)).choose (k e) := by
  have hset : (univ.filter (fun f : Π e : E, Finset (β e) => (fun e => #(f e)) = k))
      = Fintype.piFinset (fun e => (univ : Finset (β e)).powersetCard (k e)) := by
    ext f
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset, mem_powersetCard,
      Finset.subset_univ, true_and]
    constructor
    · intro h e; exact congrFun h e
    · intro h; funext e; exact h e
  rw [hset, Fintype.card_piFinset]
  exact Finset.prod_congr rfl (fun e _ => by rw [card_powersetCard, card_univ])


theorem pi_reindex_profile {M : Type*} [AddCommMonoid M] (Φ : (E → ℕ) → M) :
    (∑ f : (Π e : E, Finset (β e)), Φ (fun e => #(f e)))
      = ∑ k ∈ (univ.image (fun f : Π e : E, Finset (β e) => fun e => #(f e))),
          (∏ e : E, (Fintype.card (β e)).choose (k e)) • Φ k := by
  rw [Finset.sum_comp (fun k : E → ℕ => Φ k) (fun f : Π e : E, Finset (β e) => fun e => #(f e))]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  congr 1
  exact pi_card_profile_count k


end FluxEdgeCopy
end Sharpness
end StatMech
