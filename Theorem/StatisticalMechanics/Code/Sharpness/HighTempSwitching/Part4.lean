/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSwitching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.HighTempSources.Part3
import Def.StatisticalMechanics.Code.Sharpness.HighTempSwitching.Part2
open Finset
open scoped symmDiff


namespace StatMech

namespace Sharpness

open Ising

variable {V : Type*} [Fintype V] [DecidableEq V]


theorem highTempFirstExit_Q_congr (G : SimpleGraph V) [DecidableRel G.Adj]
    {K L : Finset (Sym2 V)} (hKL : K = L)
    (hK : K ⊆ G.edgeFinset) (hL : L ⊆ G.edgeFinset) {o z : V}
    (hbdK : HasOddBoundary K (sourcePair o z))
    (hbdL : HasOddBoundary L (sourcePair o z)) (S : Finset V)
    (ho : o ∈ S) (hz : z ∉ S) :
    (highTempFirstExit G K hK hbdK S ho hz).Q =
      (highTempFirstExit G L hL hbdL S ho hz).Q := by
  subst L
  rfl


theorem prod_pair_symmDiff_eq {α : Type*} [DecidableEq α]
    (t : α → ℝ) (F H Q : Finset α) (hQ : Q ⊆ F ∆ H) :
    (∏ e ∈ F ∆ Q, t e) * (∏ e ∈ H ∆ Q, t e) =
      (∏ e ∈ F, t e) * (∏ e ∈ H, t e) := by
  induction Q using Finset.induction_on generalizing F H with
  | empty =>
      have hF : F ∆ (∅ : Finset α) = F := by
        ext x
        simp only [Finset.mem_symmDiff, Finset.notMem_empty, not_false_eq_true,
          and_true, false_and, or_false]
      have hH : H ∆ (∅ : Finset α) = H := by
        ext x
        simp only [Finset.mem_symmDiff, Finset.notMem_empty, not_false_eq_true,
          and_true, false_and, or_false]
      rw [hF, hH]
  | @insert e Q heQ ih =>
      have heFH : e ∈ F ∆ H := hQ (by simp)
      have hpair : (F ∆ {e}) ∆ (H ∆ {e}) = F ∆ H := by
        ext x
        simp only [Finset.mem_symmDiff, Finset.mem_singleton]
        tauto
      have hQsub : Q ⊆ (F ∆ {e}) ∆ (H ∆ {e}) := by
        intro x hx
        rw [hpair]
        exact hQ (Finset.mem_insert_of_mem hx)
      have hrest := ih (F := F ∆ {e}) (H := H ∆ {e}) hQsub
      have hFin : F ∆ insert e Q = (F ∆ {e}) ∆ Q := by
        ext x
        simp only [Finset.mem_symmDiff, Finset.mem_insert,
          Finset.mem_singleton]
        by_cases hxe : x = e
        · subst x
          simp [heQ]
        · by_cases hxQ : x ∈ Q <;> simp [hxe, hxQ] <;> tauto
      have hHin : H ∆ insert e Q = (H ∆ {e}) ∆ Q := by
        ext x
        simp only [Finset.mem_symmDiff, Finset.mem_insert,
          Finset.mem_singleton]
        by_cases hxe : x = e
        · subst x
          simp [heQ]
        · by_cases hxQ : x ∈ Q <;> simp [hxe, hxQ] <;> tauto
      rw [hFin, hHin, hrest]
      rcases (Finset.mem_symmDiff.mp heFH) with ⟨heF, heH⟩ | ⟨heH, heF⟩
      · have hFs : F ∆ {e} = F.erase e := by
          ext x
          rw [mem_symmDiff_singleton_iff]
          by_cases hxe : x = e <;> simp [hxe, heF]
        have hHs : H ∆ {e} = insert e H := by
          ext x
          rw [mem_symmDiff_singleton_iff]
          by_cases hxe : x = e <;> simp [hxe, heH]
        rw [hFs, hHs, Finset.prod_insert heH,
          ← Finset.prod_erase_mul F t heF]
        ring
      · have hFs : F ∆ {e} = insert e F := by
          ext x
          rw [mem_symmDiff_singleton_iff]
          by_cases hxe : x = e <;> simp [hxe, heF]
        have hHs : H ∆ {e} = H.erase e := by
          ext x
          rw [mem_symmDiff_singleton_iff]
          by_cases hxe : x = e <;> simp [hxe, heH]
        rw [hFs, hHs, Finset.prod_insert heF,
          ← Finset.prod_erase_mul H t heH]
        ring


theorem prod_switch_erase_exit (t : Sym2 V → ℝ)
    (F H Q : Finset (Sym2 V)) {x y : V} (hQ : Q ⊆ F ∆ H)
    (heF : s(x, y) ∈ F) (heQ : s(x, y) ∉ Q) :
    (∏ e ∈ H ∆ Q, t e) * t s(x, y) *
        (∏ e ∈ (F ∆ Q).erase s(x, y), t e) =
      (∏ e ∈ F, t e) * (∏ e ∈ H, t e) := by
  have he : s(x, y) ∈ F ∆ Q := by
    exact Finset.mem_symmDiff.mpr (Or.inl ⟨heF, heQ⟩)
  have hprod := prod_pair_symmDiff_eq t F H Q hQ
  have herase := Finset.prod_erase_mul (F ∆ Q) t he
  rw [mul_comm (∏ e ∈ F ∆ Q, t e) (∏ e ∈ H ∆ Q, t e)] at hprod
  calc
    (∏ e ∈ H ∆ Q, t e) * t s(x, y) *
        (∏ e ∈ (F ∆ Q).erase s(x, y), t e) =
      (∏ e ∈ H ∆ Q, t e) *
        ((∏ e ∈ (F ∆ Q).erase s(x, y), t e) * t s(x, y)) := by ring
    _ = (∏ e ∈ H ∆ Q, t e) * (∏ e ∈ F ∆ Q, t e) := by rw [herase]
    _ = _ := hprod

end Sharpness
end StatMech
