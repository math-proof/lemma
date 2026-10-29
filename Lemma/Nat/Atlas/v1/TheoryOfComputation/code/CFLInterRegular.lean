import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.TheoryOfComputation.code.CFLInterRegular
open PDA


/--
[cfl_recognized_by_pda](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/CFLInterRegular.lean)
-/
@[path]
lemma cfl_recognized_by_pda
  {α : Type u}
  {L : Language α}
-- given
  (hL : Language.IsContextFree L) :
-- imply
  ∃ (σ : Type u) (γ : Type u) (M : PDA α σ γ), M.language = L := by
-- proof
  obtain ⟨g, rfl⟩ := hL
  exact ⟨_, _, CFGtoPDA.toPDA g, CFGtoPDA.toPDA_language g⟩
namespace PDA
variable {α : Type u} {σ₁ : Type*} {σ₂ : Type*} {γ : Type*}

namespace PDA

variable {α : Type u} {σ₁ : Type*} {σ₂ : Type*} {γ : Type*}
/--
[product_step_proj₁](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/CFLInterRegular.lean)
step of the original PDA `P` on the first component (state, input, stack). -/
@[path]
lemma product_step_proj₁ (P : PDA α σ₁ γ) (D : DFA α σ₂)
  {c₁ c₂ : Config (α := α) (σ := σ₁ × σ₂) (γ := γ)}
  (hs : (P.product D).Step c₁ c₂) :
  P.Step (c₁.1.1, c₁.2.1, c₁.2.2) (c₂.1.1, c₂.2.1, c₂.2.2) := by
  cases hs with
  | mk q q' a pop push input stack hmem =>
    obtain ⟨qp, qd⟩ := q
    simp only [product] at hmem
    cases a with
    | none =>
      obtain ⟨qp', push', hP, heq⟩ := hmem
      cases heq
      exact Step.mk qp qp' none pop push input stack hP
    | some a =>
      obtain ⟨qp', push', hP, heq⟩ := hmem
      cases heq
      exact Step.mk qp qp' (some a) pop push input stack hP

end PDA

namespace PDA

/--
[product_step_dfa_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/CFLInterRegular.lean)
-/
@[path]
lemma product_step_dfa_invariant
  {α : Type u}
  {P : PDA α σ₁ γ}
  {D : DFA α σ₂}
  {c₁ c₂ : Config (α := α) (σ := σ₁ × σ₂) (γ := γ)}
-- given
  (hs : (P.product D).Step c₁ c₂) :
-- imply
  ∃ (a : Option α), c₁.2.1 = a.toList ++ c₂.2.1 ∧ c₂.1.2 = D.evalFrom c₁.1.2 a.toList := by
-- proof
  cases hs with
  | mk q q' a pop push input stack hmem =>
    obtain ⟨qp, qd⟩ := q
    simp only [product] at hmem
    cases a with
    | none =>
      obtain ⟨qp', push', hP, heq⟩ := hmem
      cases heq
      exact ⟨none, rfl, rfl⟩
    | some a =>
      obtain ⟨qp', push', hP, heq⟩ := hmem
      cases heq
      exact ⟨some a, rfl, rfl⟩

end PDA

namespace PDA

variable {α : Type u} {σ₁ : Type*} {σ₂ : Type*} {γ : Type*}
/--
[product_reaches_proj₁](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/CFLInterRegular.lean)
PDA `P.product D` projects to a computation of `P` on the first component. -/
@[path]
lemma product_reaches_proj₁ (P : PDA α σ₁ γ) (D : DFA α σ₂)
  {c₁ c₂ : Config (α := α) (σ := σ₁ × σ₂) (γ := γ)}
  (hr : (P.product D).Reaches c₁ c₂) :
  P.Reaches (c₁.1.1, c₁.2.1, c₁.2.2) (c₂.1.1, c₂.2.1, c₂.2.2) := by
  induction hr with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact ih.tail (product_step_proj₁ P D hs)

end PDA

namespace PDA

/--
[product_reaches_dfa_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/CFLInterRegular.lean)
-/
@[path]
lemma product_reaches_dfa_invariant
  {α : Type u}
  {P : PDA α σ₁ γ}
  {D : DFA α σ₂}
  {c₁ c₂ : Config (α := α) (σ := σ₁ × σ₂) (γ := γ)}
-- given
  (hr : (P.product D).Reaches c₁ c₂) :
-- imply
  ∃ (consumed : List α), c₁.2.1 = consumed ++ c₂.2.1 ∧ c₂.1.2 = D.evalFrom c₁.1.2 consumed := by
-- proof
  induction hr with
  | refl => exact ⟨[], rfl, rfl⟩
  | tail _ hs ih =>
    obtain ⟨consumed₁, hinput₁, hdfa₁⟩ := ih
    obtain ⟨a, hinput_step, hdfa_step⟩ := product_step_dfa_invariant P D hs
    exact ⟨consumed₁ ++ a.toList,
      by rw [hinput₁, List.append_assoc, hinput_step],
      by rw [hdfa_step, hdfa₁]; simp [DFA.evalFrom, List.foldl_append]⟩

end PDA

namespace PDA

/--
[product_step_lift](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/CFLInterRegular.lean)
-/
@[path]
lemma product_step_lift
  {α : Type u}
  {P : PDA α σ₁ γ}
  {D : DFA α σ₂}
  {qd : σ₂}
  {c₁ c₂ : Config (α := α) (σ := σ₁) (γ := γ)}
-- given
  (hs : P.Step c₁ c₂) :
-- imply
  ∃ (a : Option α), c₁.2.1 = a.toList ++ c₂.2.1 ∧ (P.product D).Step ((c₁.1, qd), c₁.2.1, c₁.2.2) ((c₂.1, D.evalFrom qd a.toList), c₂.2.1, c₂.2.2) := by
-- proof
  cases hs with
  | mk qp qp' a pop push input stack hmem =>
    refine ⟨a, rfl, Step.mk (qp, qd) (qp', D.evalFrom qd a.toList) a pop push input stack ?_⟩
    simp only [product]
    cases a with
    | none => exact ⟨qp', push, hmem, rfl⟩
    | some a => exact ⟨qp', push, hmem, rfl⟩

end PDA

namespace PDA

/--
[product_reaches_of_pda_reaches](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/CFLInterRegular.lean)
-/
@[path]
lemma product_reaches_of_pda_reaches
  {α : Type u}
  {P : PDA α σ₁ γ}
  {D : DFA α σ₂}
  {qd : σ₂}
  {c₁ c₂ : Config (α := α) (σ := σ₁) (γ := γ)}
-- given
  (hr : P.Reaches c₁ c₂) :
-- imply
  ∃ (consumed : List α), c₁.2.1 = consumed ++ c₂.2.1 ∧ (P.product D).Reaches ((c₁.1, qd), c₁.2.1, c₁.2.2) ((c₂.1, D.evalFrom qd consumed), c₂.2.1, c₂.2.2) := by
-- proof
  induction hr with
  | refl => exact ⟨[], rfl, Relation.ReflTransGen.refl⟩
  | tail _ hs ih =>
    obtain ⟨consumed₁, hinput₁, hreach₁⟩ := ih
    obtain ⟨a, hinput_step, hstep_prod⟩ := product_step_lift P D (D.evalFrom qd consumed₁) hs
    refine ⟨consumed₁ ++ a.toList, ?_, ?_⟩
    · rw [hinput₁, List.append_assoc, hinput_step]
    · have : D.evalFrom (D.evalFrom qd consumed₁) a.toList =
      D.evalFrom qd (consumed₁ ++ a.toList) := by
      simp [DFA.evalFrom, List.foldl_append]
      rw [this] at hstep_prod
      exact hreach₁.tail hstep_prod

end PDA

namespace PDA

/--
[product_language](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/CFLInterRegular.lean)
-/
@[path]
lemma product_language
  {α : Type u}
  {P : PDA α σ₁ γ}
  {D : DFA α σ₂} :
-- imply
  (P.product D).language = P.language ⊓ (D.accepts : Language α) := by
-- proof
  ext w
  constructor
  ·
    intro hw
    change (P.product D).Accepts w at hw
    obtain ⟨⟨qp, qd⟩, hqacc, stack, hreach⟩ := hw
    simp only [product, Set.mem_prod] at hqacc
    constructor
    ·
      show w ∈ P.language
      exact ⟨qp, hqacc.1, stack, product_reaches_proj₁ P D hreach⟩
    ·
      obtain ⟨consumed, hinput, hdfa⟩ := product_reaches_dfa_invariant P D hreach
      simp only [product] at hinput hdfa
      have hcw : w = consumed := by simpa using hinput
      show w ∈ D.accepts
      rw [DFA.mem_accepts]
      rwa [DFA.eval, hcw, ← hdfa]
  ·
    rintro ⟨hw_pda, hw_dfa⟩
    change (P.product D).Accepts w
    obtain ⟨qp, hqp_acc, stack, hreach_p⟩ : P.Accepts w := hw_pda
    have hw_dfa' : D.eval w ∈ D.accept := D.mem_accepts.mp hw_dfa
    obtain ⟨consumed, hinput, hreach_prod⟩ :=
      product_reaches_of_pda_reaches P D D.start hreach_p
    have hcw : w = consumed := by simpa using hinput
    subst hcw
    exact ⟨(qp, D.evalFrom D.start w), by simp only [product, Set.mem_prod]; exact ⟨hqp_acc, hw_dfa'⟩,
      stack, hreach_prod⟩
end PDA
/-- **Corollary 2 (Sipser, Lecture 5).** If `A` is a context-free language and `B` is a regular
language, then `A ∩ B` is context-free.
The proof takes a PDA `P` for `A` (via the equivalence of CFGs and PDAs) and a DFA `D` for `B`,
forms the product PDA `P.product D` (which has language `L(P) ∩ L(D) = A ∩ B`), and converts
that PDA back to a CFG. -/

end PDA

/--
[product_step_proj](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/CFLInterRegular.lean)
-/
@[path]
private lemma product_step_proj_eq
  {α : Type u}
  {P : PDA α σ₁ γ}
  {D : DFA α σ₂}
  {c₁ c₂ : Config (α := α) (σ := σ₁ × σ₂) (γ := γ)}
-- given
  (hs : (P.product D).Step c₁ c₂) :
-- imply
  P.Step (c₁.1.1, c₁.2.1, c₁.2.2) (c₂.1.1, c₂.2.1, c₂.2.2) := by
-- proof
  apply PDA.product_step_proj P D hs

/--
[product_reaches_proj](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/CFLInterRegular.lean)
-/
@[path]
private lemma product_reaches_proj_eq
  {α : Type u}
  {P : PDA α σ₁ γ}
  {D : DFA α σ₂}
  {c₁ c₂ : Config (α := α) (σ := σ₁ × σ₂) (γ := γ)}
-- given
  (hr : (P.product D).Reaches c₁ c₂) :
-- imply
  P.Reaches (c₁.1.1, c₁.2.1, c₁.2.2) (c₂.1.1, c₂.2.1, c₂.2.2) := by
-- proof
  apply PDA.product_reaches_proj P D hr


-- created on 2026-10-23
-- updated on 2026-10-28
