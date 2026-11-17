/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/BellWeakExcedance.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
module

public import Mathlib.Combinatorics.Enumerative.Bell
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Tactic.Bound
public import Mathlib.Order.Partition.Finpartition
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Card
public import Def.Combinatorics.BellWeakExcedance.Part2

public section

section

namespace MetaMathlibExt

theorem root_mem (n : ℕ) (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    root n σ i ∈ wexSet n σ :=
  Nat.find_spec (exists_hit n σ i)

theorem root_eq_self (n : ℕ) (σ : Equiv.Perm (Fin n)) (i : Fin n)
    (hi : i ∈ wexSet n σ) : root n σ i = i := by
  unfold root
  have h0 : (⇑(σ ^ 0) i) ∈ wexSet n σ := by simpa using hi
  have hfind : Nat.find (exists_hit n σ i) = 0 :=
    (Nat.find_eq_zero _).mpr h0
  rw [hfind]
  simp

theorem root_le (n : ℕ) (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    root n σ i ≤ i := by
  unfold root
  suffices h : (⇑(σ ^ (Nat.find (exists_hit n σ i))) i).val ≤ i.val by
    exact Fin.mk_le_mk.mpr h
  have key : ∀ t, t ≤ Nat.find (exists_hit n σ i) →
      (⇑(σ ^ t) i).val + t ≤ i.val := by
    intro t
    induction t with
    | zero => intro _; simp
    | succ k ih =>
      intro hle
      have hlt : k < Nat.find (exists_hit n σ i) := by omega
      have hnot : (⇑(σ ^ k) i) ∉ wexSet n σ :=
        Nat.find_min (exists_hit n σ i) hlt
      simp only [wexSet, Finset.mem_filter, Finset.mem_univ, true_and] at hnot
      have hlt2 : ⇑σ (⇑(σ ^ k) i) < ⇑(σ ^ k) i := lt_of_not_ge hnot
      have hpow : ⇑(σ ^ (k + 1)) i = ⇑σ (⇑(σ ^ k) i) := by
        rw [pow_succ']
        rfl
      have ih' := ih (by omega)
      rw [hpow]
      omega
  have := key _ le_rfl
  omega

theorem root_idem (n : ℕ) (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    root n σ (root n σ i) = root n σ i :=
  root_eq_self n σ _ (root_mem n σ i)

end MetaMathlibExt
end
