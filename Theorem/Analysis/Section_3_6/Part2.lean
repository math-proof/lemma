import Mathlib
import Abbrev.Analysis.Section_3_3_api
import Abbrev.Analysis.Section_3_5.Part9
import Abbrev.Analysis.Section_3_6.Part2
/-!
# Analysis I, Section 3.6: Cardinality of sets

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Cardinality of a set
- Finite and infinite sets
- Connections with Mathlib equivalents

After this section, these notions will be deprecated in favor of their Mathlib equivalents.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/


namespace Chapter3

export SetTheory (Set Object nat)

variable [SetTheory]

theorem SetTheory.Set.has_card_iff (X:Set) (n:ℕ) :
    X.has_card n ↔ ∃ f: X → Fin n, Function.Bijective f := by
  simp [has_card, HasEquiv.Equiv, instHasEquivOfSetoid, Setoid.r, EqualCard]

/-- Example 3.6.7 -/
theorem SetTheory.Set.Example_3_6_7a (a:Object) : ({a}:Set).has_card 1 := by
  rw [has_card_iff]
  use fun _ ↦ Fin_mk _ 0 (by simp)
  constructor
  · intro x1 x2 _
    apply Subtype.ext
    exact ((mem_singleton _ _).mp x1.property).trans ((mem_singleton _ _).mp x2.property).symm
  intro y
  refine ⟨⟨a, (mem_singleton _ _).mpr rfl⟩, ?_⟩
  apply Subtype.ext
  have hy : (y : ℕ) = 0 := by have := Fin.toNat_lt y; omega
  rw [← Fin.coe_toNat y, hy]

theorem SetTheory.Set.Example_3_6_7b {a b c d:Object} (hab: a ≠ b) (hac: a ≠ c) (had: a ≠ d)
    (hbc: b ≠ c) (hbd: b ≠ d) (hcd: c ≠ d) : ({a,b,c,d}:Set).has_card 4 := by
  classical
  rw [has_card_iff]
  let f : ({a,b,c,d}:Set) → Fin 4 := fun x ↦
    Fin_mk _ (if x.val = a then 0 else if x.val = b then 1 else if x.val = c then 2 else 3)
      (by split_ifs <;> omega)
  refine ⟨f, ⟨?_, ?_⟩⟩
  · intro x y hxy
    have mem (z : ({a,b,c,d}:Set)) :
        z.val = a ∨ z.val = b ∨ z.val = c ∨ z.val = d := by
      simpa [mem_union, mem_singleton] using z.property
    have hx := mem x
    have hy := mem y
    rcases hx with hx | hx | hx | hx <;> rcases hy with hy | hy | hy | hy
    all_goals try exact Subtype.ext (hx.trans hy.symm)
    all_goals
      have hto := congrArg Fin.toNat hxy
      simp [f, hx, hy, hab.symm, hac.symm, had.symm, hbc.symm, hbd.symm, hcd.symm,
        ite_false, ite_true, Fin.toNat_mk] at hto
  · intro y
    have hy : (y:ℕ) = 0 ∨ (y:ℕ) = 1 ∨ (y:ℕ) = 2 ∨ (y:ℕ) = 3 := by
      have := Fin.toNat_lt y; omega
    rcases hy with hy | hy | hy | hy
    · refine ⟨⟨a, by simp [mem_singleton]⟩, ?_⟩
      apply Subtype.ext
      rw [← Fin.coe_toNat y, hy]
      simp [f, ite_true, Fin.toNat_mk]
    · refine ⟨⟨b, by simp [mem_singleton, hab.symm]⟩, ?_⟩
      apply Subtype.ext
      rw [← Fin.coe_toNat y, hy]
      simp [f, hab.symm, ite_false, ite_true, Fin.toNat_mk]
    · refine ⟨⟨c, by simp [mem_singleton, hac.symm, hbc.symm]⟩, ?_⟩
      apply Subtype.ext
      rw [← Fin.coe_toNat y, hy]
      simp [f, hac.symm, hbc.symm, ite_false, ite_true, Fin.toNat_mk]
    · refine ⟨⟨d, by simp [mem_singleton, had.symm, hbd.symm, hcd.symm]⟩, ?_⟩
      apply Subtype.ext
      rw [← Fin.coe_toNat y, hy]
      simp [f, had.symm, hbd.symm, hcd.symm, ite_false, Fin.toNat_mk]

/-- Proposition 3.6.8 (Uniqueness of cardinality) -/
theorem SetTheory.Set.card_uniq {X:Set} {n m:ℕ} (h1: X.has_card n) (h2: X.has_card m) : n = m := by
  -- This proof is written to follow the structure of the original text.
  revert X m; induction' n with n hn
  . intro _ _ h1 h2; rw [has_card_zero] at h1; contrapose! h1
    apply pos_card_nonempty _ h2; omega
  intro X m h1 h2
  have : X ≠ ∅ := pos_card_nonempty (by omega) h1
  choose x hx using nonempty_def this
  have : m ≠ 0 := by contrapose! this; simpa [has_card_zero, this] using h2
  specialize hn (card_erase ?_ h1 ⟨ _, hx ⟩) (card_erase ?_ h2 ⟨ _, hx ⟩) <;> omega

lemma SetTheory.Set.Example_3_6_8_a: ({0,1,2}:Set).has_card 3 := by
  rw [has_card_iff]
  have : ({0, 1, 2}: Set) = SetTheory.Set.Fin 3 := by
    ext x
    simp only [mem_insert, mem_singleton, mem_Fin]
    constructor
    · aesop
    rintro ⟨x, ⟨_, rfl⟩⟩
    simp only [nat_coe_eq_iff]
    omega
  rw [this]
  use id
  exact Function.bijective_id

lemma SetTheory.Set.Example_3_6_8_b: ({3,4}:Set).has_card 2 := by
  rw [has_card_iff]
  classical
  have hne : (3:Object) ≠ 4 := fun h => (by decide : (3:ℕ) ≠ 4) ((Object.natCast_inj 3 4).mp h)
  let f : ({3,4}:Set) → Fin 2 := fun x ↦
    Fin_mk _ (if x.val = 3 then 0 else 1) (by split_ifs <;> omega)
  refine ⟨f, ⟨?_, ?_⟩⟩
  · intro x y hxy
    have hx : x.val = 3 ∨ x.val = 4 := by simpa [mem_union, mem_singleton] using x.property
    have hy : y.val = 3 ∨ y.val = 4 := by simpa [mem_union, mem_singleton] using y.property
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact Subtype.ext (hx.trans hy.symm)
    · have hto := congrArg Fin.toNat hxy
      simp only [f, Fin.toNat_mk, hx, hy, hne.symm, ite_true, ite_false] at hto
      omega
    · have hto := congrArg Fin.toNat hxy
      simp only [f, Fin.toNat_mk, hx, hy, hne.symm, ite_true, ite_false] at hto
      omega
    · exact Subtype.ext (hx.trans hy.symm)
  · intro y
    have hy : (y:ℕ) = 0 ∨ (y:ℕ) = 1 := by have := Fin.toNat_lt y; omega
    rcases hy with hy | hy
    · refine ⟨⟨3, by simp [mem_singleton]⟩, ?_⟩
      apply Subtype.ext
      rw [← Fin.coe_toNat y, hy]
      simp [f, ite_true, Fin.toNat_mk]
    · refine ⟨⟨4, by simp [mem_singleton]⟩, ?_⟩
      apply Subtype.ext
      rw [← Fin.coe_toNat y, hy]
      simp [f, hne.symm, ite_false, Fin.toNat_mk]

lemma SetTheory.Set.Example_3_6_8_c : ¬({0,1,2}:Set) ≈ ({3,4}:Set) := by
  by_contra h
  have h1 : Fin 3 ≈ Fin 2 := (Example_3_6_8_a.symm.trans h).trans Example_3_6_8_b
  have h2 : Fin 3 ≈ Fin 3 := by rfl
  have := card_uniq h1 h2
  contradiction

end Chapter3
