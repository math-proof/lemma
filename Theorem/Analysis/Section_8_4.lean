import Mathlib
import Theorem.Analysis.Section_8_1.Part4
import Theorem.Analysis.Section_8_2.Part4
import Def.Analysis.Section_8_4
set_option doc.verso.suggestions false

/-!
# Analysis I, Section 8.4: The axiom of choice

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Review of Mathlib's dependent product type `∀ α, X α`.
- The axiom of choice in various equivalent forms, as well as the countable axiom of choice.

As the Chapter 3 set theory has been deprecated for many chapters at this point, we will not insert the axiom of choice directly into that theory in this text; but this could be accomplished if desired
(e.g., by extending the `Chapter3.SetTheory` class to a `Chapter3.SetTheoryWithChoice` class), and
students are welcome to attempt this separately.  Instead, we will use Mathlib's native
{name}`Classical.choice` axiom.  Technically, this axiom has already been used quite frequently in the
text already, in large part because Mathlib uses {name}`Classical.choice` to derive many weaker statements,
such as the law of the excluded middle.  So the distinctions made in the original text regarding
whether a given statement or not uses the axiom of choice are somewhat blurred in this formalization.
It is theoretically possible to restore this distinction by removing the reliance on Mathlib and
working throughout with custom structures such as `Chapter3.SetTheory` and
`Chapter3.SetTheoryWithChoice`, but this would be extremely tedious and not attempted here.
-/


namespace Chapter8

/-- Axiom 8.1 (Choice) -/
theorem axiom_of_choice {I: Type} {X: I → Type} (h : ∀ i, Nonempty (X i)) :
  Nonempty (∀ i, X i) := by use fun i ↦ (h i).some

theorem axiom_of_countable_choice {I: Type} {X: I → Type} [Countable I] (h : ∀ i, Nonempty (X i)) :
  Nonempty (∀ i, X i) := axiom_of_choice h

/-- Lemma 8.4.5 -/
theorem exist_tendsTo_sup {E: Set ℝ} (hnon: E.Nonempty) (hbound: BddAbove E) :
  ∃ a : ℕ → ℝ, (∀ n, a n ∈ E) ∧ Filter.atTop.Tendsto a (nhds (sSup E)) := by
  -- This proof is written to follow the structure of the original text.
  set X : ℕ → Set ℝ := fun n ↦ { x ∈ E | sSup E - 1 / (n+1:ℝ) ≤ x ∧ x ≤ sSup E }
  have hX : ∀ n, Nonempty (X n) := by
    intro n
    have : 1 / (n+1:ℝ) > 0 := by positivity
    choose s hs using (lt_csSup_iff hbound hnon).mp (show sSup E - 1 / (n+1:ℝ) < sSup E by linarith)
    use s; simp_all [X]
    refine ⟨ by linarith, le_csSup hbound hs.1 ⟩
  have ⟨ a ⟩ := axiom_of_countable_choice hX
  use fun n ↦ ↑(a n); constructor; swap
  apply Filter.Tendsto.squeeze (g := fun n:ℕ ↦ sSup E - 1/(n+1:ℝ)) (h := fun _:ℕ ↦ sSup E)
  . convert tendsto_const_nhds.sub (a := sSup E) (b := 0) _; simp
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  . exact tendsto_const_nhds
  all_goals intro n; have := (a n).property; simp_all [X]

/-- Remark 8.4.6.  This special case of Lemma 8.4.5 avoids (countable) choice. -/
theorem exist_tendsTo_sup_of_closed {E: Set ℝ} (hnon: E.Nonempty) (hbound: BddAbove E) (hclosed: IsClosed E) :
  ∃ a : ℕ → ℝ, (∀ n, a n ∈ E) ∧ Filter.atTop.Tendsto a (nhds (sSup E)) := by
  set X : ℕ → Set ℝ := fun n ↦ { x ∈ E | sSup E - 1 / (n+1:ℝ) ≤ x ∧ x ≤ sSup E }
  have hX : ∀ n, Nonempty (X n) := by
    intro n
    have : 1 / (n+1:ℝ) > 0 := by positivity
    choose s hs using (lt_csSup_iff hbound hnon).mp (show sSup E - 1 / (n+1:ℝ) < sSup E by linarith)
    use s; simp_all [X]
    refine ⟨ by linarith, le_csSup hbound hs.1 ⟩
  set a : ℕ → ℝ := fun n ↦ sInf (X n)
  have ha (n:ℕ) : a n ∈ X n := by
    apply IsClosed.csInf_mem _ Set.Nonempty.of_subtype
    . rw [bddBelow_def]; use sSup E - 1 / (n+1:ℝ); aesop
    . rw [show X n = E ∩ .Icc (sSup E - 1 / (n+1:ℝ)) (sSup E) by ext; aesop]
      exact hclosed.inter isClosed_Icc
  use a; constructor; swap
  apply Filter.Tendsto.squeeze (g := fun n:ℕ ↦ sSup E - 1/(n+1:ℝ)) (h := fun _:ℕ ↦ sSup E)
  . convert tendsto_const_nhds.sub (a := sSup E) (b := 0) _; simp
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  . exact tendsto_const_nhds
  all_goals intro _; simp_all [X]

end Chapter8
