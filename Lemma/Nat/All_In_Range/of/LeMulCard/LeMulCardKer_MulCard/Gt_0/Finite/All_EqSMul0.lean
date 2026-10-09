import Mathlib
import sympy.Basic


/--
[AddMonoidHom_mem_range_of_smul_eq_zero_of_natCard_ker_mul_le_of_natCard_mul_le](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AddMonoidHom_mem_range_of_smul_eq_zero_of_natCard_ker_mul_le_of_natCard_mul_le.lean)
-/
@[path]
private lemma main
  {T J : Type*} [AddCommGroup T] [AddCommGroup J] [Finite T]
  {f : T →+ J}
  {q : ℤ}
  {X Y : ℕ}
-- given
  (hT : ∀ t : T, q • t = 0)
  (hfinJ : Finite {x : J // q • x = 0})
  (hY : 0 < Y)
  (hker : Nat.card f.ker * X ≤ Nat.card T * Y)
  (hJ : Nat.card {x : J // q • x = 0} * Y ≤ X) :
-- imply
  ∀ x : J, q • x = 0 → x ∈ f.range := by
-- proof
  classical
  have := hfinJ

  let ι : f.range → {x : J // q • x = 0} := fun y => ⟨y.1, by
    obtain ⟨t, ht⟩ := y.2
    rw [← ht, ← map_zsmul, hT, map_zero]⟩
  have hι : Function.Injective ι := by
    intro a b h
    have h' : ((ι a : {x : J // q • x = 0}) : J) = ((ι b : {x : J // q • x = 0}) : J) := congrArg Subtype.val h
    exact Subtype.ext h'

  have hT' : Nat.card T = Nat.card f.ker * Nat.card f.range := by
    rw [(f.ker).card_eq_card_quotient_mul_card_addSubgroup,
      Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv, mul_comm]
  have hkpos : 0 < Nat.card f.ker := Nat.card_pos

  have h1 : X ≤ Nat.card f.range * Y := by
    have h := hker
    rw [hT', mul_assoc] at h
    exact Nat.le_of_mul_le_mul_left h hkpos
  have h2 : Nat.card {x : J // q • x = 0} ≤ Nat.card f.range :=
    Nat.le_of_mul_le_mul_right (hJ.trans h1) hY
  have hbij : Function.Bijective ι := hι.bijective_of_nat_card_le h2
  intro x hx
  obtain ⟨y, hy⟩ := hbij.2 ⟨x, hx⟩
  have : (y : J) = x := congrArg Subtype.val hy
  rw [← this]
  exact y.2


-- created on 2026-10-05
