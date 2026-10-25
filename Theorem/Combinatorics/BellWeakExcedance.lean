/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/BellWeakExcedance.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Combinatorics.Enumerative.Bell
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.Bound
import Mathlib.Order.Partition.Finpartition
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Def.Combinatorics.BellWeakExcedance


section

namespace MetaMathlibExt

theorem exists_hit (n : ℕ) (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    ∃ t, ⇑(σ ^ t) i ∈ wexSet n σ := by
  by_contra h
  simp only [not_exists] at h
  have desc : ∀ t, (⇑(σ ^ (t + 1)) i).val < (⇑(σ ^ t) i).val := by
    intro t
    have hmem := h t
    simp only [wexSet, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    have hlt : ⇑σ (⇑(σ ^ t) i) < ⇑(σ ^ t) i := lt_of_not_ge hmem
    have hpow : ⇑(σ ^ (t + 1)) i = ⇑σ (⇑(σ ^ t) i) := by
      rw [pow_succ']
      rfl
    rw [hpow]
    exact hlt
  have bound : ∀ t, (⇑(σ ^ t) i).val + t ≤ i.val := by
    intro t
    induction t with
    | zero => simp
    | succ k ih =>
      have dk := desc k
      omega
  have hlast := bound (i.val + 1)
  omega

end MetaMathlibExt
end
