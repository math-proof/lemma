/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Additive/MinimumRestrictedAdditiveBasis.lean -/


import sympy.atlas.Combinatorics.Additive.MinimumRestrictedAdditiveBasis
import Mathlib.Tactic

open MetaMathlibExt

example (s : ℕ) :
    (minimumRestrictedAdditiveBasisCard s).val = none ↔ s % 2 = 1 :=
  minimumRestrictedAdditiveBasisCard_eq_none_iff s

example (s : ℕ) :
    (minimumRestrictedAdditiveBasisCard s).val.isSome ↔ s % 2 = 0 :=
  minimumRestrictedAdditiveBasisCard_isSome_iff s

-- The value at `s = 1` is `none`.
example : (minimumRestrictedAdditiveBasisCard 1).val = none := by
  apply (minimumRestrictedAdditiveBasisCard_eq_none_iff 1).2
  decide

-- The value at `s = 0` is `some 1`.
example : (minimumRestrictedAdditiveBasisCard 0).val = some 1 := by
  have hprop := (minimumRestrictedAdditiveBasisCard 0).property
  have h0bound : ∀ a ∈ ({0} : Finset Nat), 2 * a ≤ 0 := by
    intro a ha
    rw [Finset.mem_singleton] at ha
    omega
  have h0cover : ∀ x : Nat, x ≤ 0 →
      ∃ a ∈ ({0} : Finset Nat), ∃ b ∈ ({0} : Finset Nat), a + b = x := by
    intro x hx
    have hx0 : x = 0 := by omega
    subst hx0
    exact ⟨0, by decide, 0, by decide, rfl⟩
  cases hval : (minimumRestrictedAdditiveBasisCard 0).val with
  | none =>
    have hno := hprop.2 hval
    exact absurd ⟨{0}, h0bound, h0cover⟩ hno
  | some k =>
    have hsome := (hprop.1 k hval).1
    obtain ⟨A, hbound, hcover, hcard⟩ := hsome
    have hmin := (hprop.1 k hval).2
    have hle : k ≤ 1 := by
      have hmem := hmin {0} h0bound h0cover
      have hcard0 : ({0} : Finset Nat).card = 1 := by decide
      omega
    have hge : 1 ≤ k := by
      obtain ⟨a, haA, b, -, -⟩ := hcover 0 le_rfl
      have hne : A.Nonempty := ⟨a, haA⟩
      have hpos : 0 < A.card := Finset.card_pos.mpr hne
      omega
    have hk1 : k = 1 := by omega
    rw [hk1]

-- The value at `s = 2` is `some 2`.
example : (minimumRestrictedAdditiveBasisCard 2).val = some 2 := by
  have hprop := (minimumRestrictedAdditiveBasisCard 2).property
  have h01bound : ∀ a ∈ ({0, 1} : Finset Nat), 2 * a ≤ 2 := by
    intro a ha
    rw [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl <;> decide
  have h01cover : ∀ x : Nat, x ≤ 2 → ∃ a ∈ ({0, 1} : Finset Nat),
      ∃ b ∈ ({0, 1} : Finset Nat), a + b = x := by
    intro x hx
    interval_cases x
    · exact ⟨0, by decide, 0, by decide, rfl⟩
    · exact ⟨0, by decide, 1, by decide, rfl⟩
    · exact ⟨1, by decide, 1, by decide, rfl⟩
  cases hval : (minimumRestrictedAdditiveBasisCard 2).val with
  | none =>
    have hno := hprop.2 hval
    exact absurd ⟨{0, 1}, h01bound, h01cover⟩ hno
  | some k =>
    have hsome := (hprop.1 k hval).1
    obtain ⟨A, hbound, hcover, hcard⟩ := hsome
    have hmin := (hprop.1 k hval).2
    have hle : k ≤ 2 := by
      have hmem := hmin {0, 1} h01bound h01cover
      have hcard01 : ({0, 1} : Finset Nat).card = 2 := by decide
      omega
    have hge : 2 ≤ k := by
      obtain ⟨a, haA, b, hbA, hab⟩ := hcover 0 (by omega)
      have ha0 : a = 0 := by omega
      have h0A : (0 : Nat) ∈ A := ha0 ▸ haA
      obtain ⟨c, hcA, d, hdA, hcd⟩ := hcover 1 (by omega)
      have h1A : (1 : Nat) ∈ A := by
        by_cases hc0 : c = 0
        · have hd1 : d = 1 := by omega
          exact hd1 ▸ hdA
        · have hc1 : c = 1 := by omega
          exact hc1 ▸ hcA
      have hsub : ({0, 1} : Finset Nat) ⊆ A := by
        intro y hy
        rw [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl
        · exact h0A
        · exact h1A
      have hcard01 : ({0, 1} : Finset Nat).card = 2 := by decide
      have hlecard : ({0, 1} : Finset Nat).card ≤ A.card :=
        Finset.card_le_card hsub
      omega
    have hk2 : k = 2 := by omega
    rw [hk2]
