import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Notation.Fun
import Initialize.Tactic.Attr.Basic


/--
`MeasurableSet S` means that `S` lies in the σ-algebra chosen by the ambient
measurable space, which is a genuine σ-algebra on `α`.
-/
@[path]
private lemma main
  [MeasurableSpace α]
  {S : Set α}
-- given
  (h : MeasurableSet S) :
-- imply
  ∃ σ : Set (Set α),
    (∅ ∈ σ ∧
      (∀ s : Set α, s ∈ σ → sᶜ ∈ σ) ∧
      (∀ f : ℕ ⇀ Set α, (∀ i : ℕ, f[i] ∈ σ) → (⋃ i : ℕ, f[i]) ∈ σ)) ∧
    S ∈ σ :=
-- proof
  ⟨{s | MeasurableSet s},
    ⟨MeasurableSet.empty,
      fun _ hs => hs.compl,
      fun _ hf => MeasurableSet.iUnion hf⟩,
    h⟩


-- created on 2026-11-19
