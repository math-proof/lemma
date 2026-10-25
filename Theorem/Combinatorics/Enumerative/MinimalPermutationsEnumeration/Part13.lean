/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MinimalPermutationsEnumeration.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.Fin.Rev
import Mathlib.Order.Fin.Basic
import Def.Combinatorics.Enumerative.MinimalPermutationsEnumeration.Part12


section

namespace MetaMathlibExt

theorem mpeFiber_ascent (d : ℕ) (a : Fin (d + 1))
    (σ : Equiv.Perm (Fin (d + 2))) (hσ : σ ∈ mpeFiber d a) :
    mpeGood d σ ∧
      (Finset.univ.filter fun i : Fin (d + 1) =>
        σ i.castSucc < σ i.succ) = {a} := by
  have hfiber := Finset.mem_filter.mp hσ
  have hgood := (mpePerms_mem d σ).mp hfiber.1
  obtain ⟨_, _, hasc, _⟩ := mpeAscentPos_spec d σ hgood
  rw [hfiber.2] at hasc
  exact ⟨hgood, hasc⟩

theorem mpeFiber_firstVals_mem (d : ℕ) (a : Fin (d + 1))
    (hpos : 0 < a.val) (σ : Equiv.Perm (Fin (d + 2))) (hσ : σ ∈ mpeFiber d a) :
    firstVals d σ a ∈ mpeAllowed d a hpos := by
  have hfiber := Finset.mem_filter.mp hσ
  have hgood := (mpePerms_mem d σ).mp hfiber.1
  have haeq := hfiber.2
  subst a
  obtain ⟨_, _, _, hallowed⟩ := mpeAscentPos_spec d σ hgood
  apply (mpeAllowed_mem d (mpeAscentPos d σ) hpos _).mpr
  exact ⟨firstVals_card d σ (mpeAscentPos d σ), hallowed⟩

theorem mpeConstruct_mem_fiber (d : ℕ) (a : Fin (d + 1))
    (hpos : 0 < a.val) (hlt : a.val < d) (L : Finset (Fin (d + 2)))
    (hL : L.card = a.val + 1)
    (hallowed : L ∉ exclA d a hpos ∪ exclB d a) :
    mpeConstruct d a L hL ∈ mpeFiber d a := by
  have hB : L ∉ exclB d a := by
    intro hmem
    exact hallowed (Finset.mem_union.mpr (Or.inr hmem))
  have hasc := mpeConstruct_ascent_singleton d a L hL hB
  have hfirst := mpeConstruct_firstVals d a L hL
  have hallowed' : firstVals d (mpeConstruct d a L hL) a ∉
      exclA d a hpos ∪ exclB d a := by
    rw [hfirst]
    exact hallowed
  have hgood := mpeGood_backward d (mpeConstruct d a L hL) a hpos hlt hasc hallowed'
  have hposEq : mpeAscentPos d (mpeConstruct d a L hL) = a := by
    obtain ⟨_, _, hasc', _⟩ := mpeAscentPos_spec d (mpeConstruct d a L hL) hgood
    have hmem : mpeAscentPos d (mpeConstruct d a L hL) ∈ ({a} : Finset _) := by
      rw [← hasc, hasc']
      exact Finset.mem_singleton_self _
    exact Finset.mem_singleton.mp hmem
  apply Finset.mem_filter.mpr
  exact ⟨(mpePerms_mem d _).mpr hgood, hposEq⟩

theorem mpeFiber_card_allowed (d : ℕ) (a : Fin (d + 1))
    (hpos : 0 < a.val) (hlt : a.val < d) :
    (mpeFiber d a).card = (mpeAllowed d a hpos).card := by
  classical
  apply Finset.card_bij
    (fun σ _ => firstVals d σ a)
    (fun σ hσ => mpeFiber_firstVals_mem d a hpos σ hσ)
  · intro σ₁ hσ₁ σ₂ hσ₂ heq
    have ha₁ := (mpeFiber_ascent d a σ₁ hσ₁).2
    have ha₂ := (mpeFiber_ascent d a σ₂ hσ₂).2
    exact mpe_reconstruct_injective d σ₁ σ₂ a ha₁ ha₂ heq
  · intro L hmem
    obtain ⟨hL, hallowed⟩ := (mpeAllowed_mem d a hpos L).mp hmem
    refine ⟨mpeConstruct d a L hL,
      mpeConstruct_mem_fiber d a hpos hlt L hL hallowed, ?_⟩
    exact mpeConstruct_firstVals d a L hL

end MetaMathlibExt
end
