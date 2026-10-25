import Mathlib
import Abbrev.Analysis.Section_3_1_api
import Abbrev.Analysis.Section_3_4.Part4
/-!
# Analysis I, Section 3.4: Images and inverse images

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Images and inverse images of (Mathlib) functions, within the framework of Section 3.1 set
  theory. (The Section 3.3 functions are now deprecated and will not be used further.)
- Connection with Mathlib's image {syntax term}`f '' S` and preimage {syntax term}`f ⁻¹' S` notions.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/


namespace Chapter3

export SetTheory (Set Object nat)

variable [SetTheory]

theorem SetTheory.Set.example_3_4_9 (F:Object) :
    F ∈ ({0,1}:Set) ^ ({4,7}:Set) ↔ F = f_3_4_9_a
    ∨ F = f_3_4_9_b ∨ F = f_3_4_9_c ∨ F = f_3_4_9_d := by
  rw [powerset_axiom]
  refine ⟨?_, by aesop ⟩
  rintro ⟨f, rfl⟩
  have h1 := (f ⟨4, by simp [SetTheory.Set.mem_singleton]⟩).property
  have h2 := (f ⟨7, by simp [SetTheory.Set.mem_singleton]⟩).property
  simp [coe_of_fun_inj, SetTheory.Set.mem_singleton] at *
  obtain _ | _ := h1 <;> obtain _ | _ := h2
  map_tacs [left; (right;left); (right;right;left); (right;right;right)]
  all_goals
    ext ⟨val, hx⟩
    simp [SetTheory.Set.mem_pair, SetTheory.Set.mem_singleton] at hx
    rcases hx with rfl | rfl
    · simp [f_3_4_9_a, f_3_4_9_b, f_3_4_9_c, f_3_4_9_d, *]
    · have hne : ¬ ((7:Object) = 4) := by
        intro h
        have := (Object.natCast_inj 7 4).mp h
        contradiction
      simp [hne, f_3_4_9_a, f_3_4_9_b, f_3_4_9_c, f_3_4_9_d, *]

/-- Lemma 3.4.10 -/
theorem SetTheory.Set.exists_powerset (X:Set) :
   ∃ (Z: Set), ∀ x, x ∈ Z ↔ ∃ Y:Set, x = Y ∧ Y ⊆ X := by
  use powerset X; apply mem_powerset

/- As noted in errata, Exercise 3.4.6 (ii) is replaced by Exercise 3.5.11. -/

/-- Remark 3.4.11 -/
theorem SetTheory.Set.powerset_of_triple (a b c x:Object) :
    x ∈ powerset {a,b,c}
    ↔ x = (∅:Set)
    ∨ x = ({a}:Set)
    ∨ x = ({b}:Set)
    ∨ x = ({c}:Set)
    ∨ x = ({a,b}:Set)
    ∨ x = ({a,c}:Set)
    ∨ x = ({b,c}:Set)
    ∨ x = ({a,b,c}:Set) := by
  simp only [mem_powerset, subset_def, mem_triple]
  refine ⟨ ?_, ?_ ⟩
  · rintro ⟨Y, rfl, hY⟩; by_cases a ∈ Y <;> by_cases b ∈ Y <;> by_cases c ∈ Y
    on_goal 8 => left
    on_goal 4 => right; left
    on_goal 6 => right; right; left
    on_goal 7 => right; right; right; left
    on_goal 2 => right; right; right; right; left
    on_goal 3 => right; right; right; right; right; left
    on_goal 5 => right; right; right; right; right; right; left
    on_goal 1 => right; right; right; right; right; right; right
    all_goals congr; ext; simp [SetTheory.Set.mem_singleton, SetTheory.Set.mem_pair]; grind
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      simp [subset_def, mem_triple, SetTheory.Set.mem_singleton, SetTheory.Set.mem_pair]

/-- Axiom 3.12 (Union) -/
theorem SetTheory.Set.union_axiom (A: Set) (x:Object) :
    x ∈ union A ↔ ∃ (S:Set), x ∈ S ∧ (S:Object) ∈ A := SetTheory.union_axiom A x

/-- Connection with Mathlib union -/
theorem SetTheory.Set.union_eq (A: Set) :
    (union A : _root_.Set Object) =
    ⋃₀ { S : _root_.Set Object | ∃ S':Set, S = S' ∧ (S':Object) ∈ A } := by
  ext; simp [union_axiom, Set.mem_sUnion]; aesop

end Chapter3
