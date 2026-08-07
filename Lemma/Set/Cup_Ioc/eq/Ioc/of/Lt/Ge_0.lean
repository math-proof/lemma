import Lemma.Set.Cup.eq.UnionCupS
import Lemma.Set.Cup_Ioc.eq.Ioc0.of.Ge_0
import Lemma.Nat.Ge.of.Ge.Gt
open Set Nat


@[main]
private lemma main
  [Ring R] [LinearOrder R] [IsStrictOrderedRing R]
  {a b : ℤ}
-- given
  (h_a : a ≥ 0)
  (h_ab : a < b) :
-- imply
  ⋃ k ∈ Ico a b, Ioc (k : R) (k + 1 : R) = Ioc (a : R) (b : R) := by
-- proof
  set f : ℤ → Set R := fun k => Ioc (k : R) (k + 1 : R)
  if ha : a = 0 then
    subst ha
    simpa [f] using Cup_Ioc.eq.Ioc0.of.Ge_0 (le_of_lt h_ab)
  else
    have h_b := Ge.of.Ge.Gt h_ab h_a
    have h_cup_a := Cup_Ioc.eq.Ioc0.of.Ge_0 (R := R) h_a
    have h_cup_b := Cup_Ioc.eq.Ioc0.of.Ge_0 (R := R) h_b
    rw [Cup.eq.UnionCupS f (Ico 0 b) (Ico 0 a)] at h_cup_b
    have h_inter : Ico 0 b ∩ Ico 0 a = Ico 0 a := by grind
    have h_sdiff : Ico 0 b \ Ico 0 a = Ico a b := by grind
    rw [h_inter, h_sdiff] at h_cup_b
    have h_disjoint : (⋃ k ∈ Ico 0 a, f k) ∩ ⋃ k ∈ Ico a b, f k ⊆ ∅ := by
      intro x ⟨hx_a, hx_ab⟩
      rw [h_cup_a] at hx_a
      obtain ⟨hx0, hxa⟩ := hx_a
      rw [In_Cup.is.Any_In.set] at hx_ab
      obtain ⟨k, ⟨hka, _⟩, hx_in_f⟩ := hx_ab
      simp only [f, Set.mem_Ioc] at hx_in_f
      exact not_lt.mpr hka (by exact_mod_cast lt_of_lt_of_le hx_in_f.left hxa)
    have h_union : ⋃ k ∈ Ico a b, f k = Ioc (0 : R) (b : R) \ Ioc (0 : R) (a : R) := by
      have h_eq : (⋃ x ∈ Ico 0 a, f x) ∪ ⋃ x ∈ Ico a b, f x = Ioc (0 : R) (b : R) := by
        simpa [h_cup_a] using h_cup_b
      rw [← h_eq, ← h_cup_a]
      rw [Set.union_comm]
      symm
      apply Set.union_sdiff_cancel_right
      intro x ⟨hx_ab, hx_a⟩
      simpa [Set.mem_empty_iff_false] using h_disjoint ⟨hx_a, hx_ab⟩
    have h_ioc : Ioc (0 : R) (b : R) \ Ioc (0 : R) (a : R) = Ioc (a : R) (b : R) := by
      ext x
      constructor
      ·
        intro h
        rw [Set.mem_sdiff, Set.mem_Ioc] at h
        obtain ⟨⟨hx0, hxb⟩, hx_not_a⟩ := h
        rw [Set.mem_Ioc] at hx_not_a
        refine ⟨?_, hxb⟩
        if hlt : (a : R) < x then
          exact hlt
        else
          have hxa' : x ≤ (a : R) := le_of_not_gt hlt
          exact absurd ⟨hx0, hxa'⟩ hx_not_a
      ·
        intro h
        rw [Set.mem_Ioc] at h
        obtain ⟨hxa, hxb⟩ := h
        have ha_pos : (0 : R) < (a : R) := by exact_mod_cast show (0 : ℤ) < a by omega
        rw [Set.mem_sdiff, Set.mem_Ioc]
        refine ⟨⟨lt_trans ha_pos hxa, hxb⟩, ?_⟩
        rw [Set.mem_Ioc]
        intro ⟨_, hxa'⟩
        exact not_lt.mpr hxa' hxa
    simpa [f] using h_union.trans h_ioc


-- created on 2018-09-17
-- updated on 2026-08-07
