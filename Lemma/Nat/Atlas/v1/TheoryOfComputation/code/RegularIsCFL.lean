import Mathlib
import sympy.Basic
import Def.v1.Atlas.TheoryOfComputation.code.RegularIsCFL
open RegularIsCFL
open Computability


namespace RegularIsCFL

/--
[dfaToPDA_step_characterize](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/RegularIsCFL.lean)
-/
@[path]
lemma dfaToPDA_step_characterize
  {α : Type u}
  {D : DFA α σ}
  {c₁ c₂ : σ × List α × List PUnit}
-- given
  (h : (dfaToPDA D).Step c₁ c₂) :
-- imply
  ∃ a : α, c₁.2.1 = a :: c₂.2.1 ∧ c₂.1 = D.step c₁.1 a ∧ c₂.2.2 = c₁.2.2 := by
-- proof
  obtain ⟨q₁, w₁, s₁⟩ := c₁
  obtain ⟨q₂, w₂, s₂⟩ := c₂
  simp only
  cases h with
  | mk _ _ a pop push input stack hmem =>
    simp only [dfaToPDA] at hmem
    split at hmem
    · rename_i a
      simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      obtain ⟨rfl, rfl⟩ := hmem
      exact ⟨a, by simp [Option.toList], rfl, rfl⟩
    · exact absurd hmem (Set.notMem_empty _)

end RegularIsCFL

namespace RegularIsCFL

/--
[dfaToPDA_reaches_evalFrom](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/RegularIsCFL.lean)
-/
@[path]
lemma dfaToPDA_reaches_evalFrom
  {α : Type u}
  {D : DFA α σ}
  {q : σ}
  {w : List α} :
-- imply
  (dfaToPDA D).Reaches (q, w, []) (D.evalFrom q w, [], []) := by
-- proof
  induction w generalizing q with
  | nil =>
    exact Relation.ReflTransGen.refl
  | cons a w ih =>
    apply Relation.ReflTransGen.head
    · have hmem : (D.step q a, (none : Option PUnit)) ∈
      (dfaToPDA D).step q (some a) none := by
      simp [dfaToPDA]
      exact PDA.Step.mk q (D.step q a) (some a) none none w [] hmem
    · exact ih (D.step q a)

end RegularIsCFL

namespace RegularIsCFL

/--
[dfaToPDA_reaches_inv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/RegularIsCFL.lean)
-/
@[path]
lemma dfaToPDA_reaches_inv
  {α : Type u}
  {D : DFA α σ}
  {c₁ c₂ : σ × List α × List PUnit}
-- given
  (hreach : (dfaToPDA D).Reaches c₁ c₂)
  (hs : c₁.2.2 = []) :
-- imply
  c₂.2.2 = [] ∧ ∃ pref : List α, c₁.2.1 = pref ++ c₂.2.1 ∧ c₂.1 = D.evalFrom c₁.1 pref := by
-- proof
  induction hreach with
  | refl =>
    exact ⟨hs, [], by simp [DFA.evalFrom]⟩
  | tail _ hstep ih =>
    obtain ⟨hs_mid, pref, hw_mid, hq_mid⟩ := ih
    obtain ⟨a, hw_step, hq_step, hs_step⟩ := dfaToPDA_step_characterize D hstep
    refine ⟨hs_step ▸ hs_mid, pref ++ [a], ?_, ?_⟩
    · rw [hw_mid, List.append_assoc, List.singleton_append, hw_step]
    · simp [DFA.evalFrom, List.foldl_append, hq_mid, hq_step]

end RegularIsCFL

namespace RegularIsCFL

/--
[dfaToPDA_language](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/RegularIsCFL.lean)
-/
@[path]
lemma dfaToPDA_language
  {α : Type u}
  {D : DFA α σ} :
-- imply
  (dfaToPDA D).language = D.accepts := by
-- proof
  ext w
  simp only [PDA.language, PDA.Accepts, DFA.mem_accepts]
  constructor
  ·
    rintro ⟨q, hq, stack, hreach⟩
    obtain ⟨_, pref, hw_eq, hq_eq⟩ := dfaToPDA_reaches_inv D hreach rfl
    change q = D.evalFrom D.start pref at hq_eq
    change w = pref ++ [] at hw_eq
    simp only [List.append_nil] at hw_eq
    simp only [dfaToPDA] at hq
    subst hw_eq; subst hq_eq
    exact hq
  ·
    intro haccept
    exact ⟨D.eval w, haccept, [], dfaToPDA_reaches_evalFrom D D.start w⟩

end RegularIsCFL

namespace RegularIsCFL

/--
[regular_is_cfl](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/RegularIsCFL.lean)
-/
@[path]
lemma regular_is_cfl
  {α : Type u}
  {α : Type u}
  {A : Language α}
-- given
  (h : A.IsRegular) :
-- imply
  Language.IsContextFree A := by
-- proof
  obtain ⟨σ_type, _, D, hD⟩ := h
  rw [show A = (dfaToPDA D : PDA α σ_type (PUnit : Type)).language from
    by rw [dfaToPDA_language]; exact hD.symm]
  exact pda_language_isContextFree _

end RegularIsCFL


-- created on 2026-10-23
