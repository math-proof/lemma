import Mathlib
import Instance.Analysis.MeasureTheory.Notation.Part2
open Filter


/-- Axiom 0.0.4 (Axiom of choice). -/
noncomputable def Set.choose {A: Type*} {E: A → Type*} (hE: ∀ n, Nonempty (E n)) :
∀ n, E n := fun n ↦ (hE n).some

/-- Corollary 0.0.5 (Axiom of countable choice) -/
noncomputable def Countable.choose {E: ℕ → Type*} (hE: ∀ n, Nonempty (E n)) :
∀ n, E n := Set.choose hE

