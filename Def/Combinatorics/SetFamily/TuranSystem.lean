/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SetFamily/TuranSystem.lean -/

import Mathlib.Data.Fintype.Basic
import Def.Combinatorics.SetFamily.UniformHypergraph
import Lemma.Finset.SetFamily.UniformHypergraph
/-!
Turan systems after Liu and Pikhurko,
"A note on the minimum size of Turán systems" (arXiv:2501.15457v2).
Tracks source lines 138-139, 148, and 150-152 for the covering definition.
-/


namespace TuranSystem

/-- `IsTuranSystem n s r H` means `H` is `r`-uniform and every `s`-set
contains an edge of `H`, with `0 < r ∧ r < s ∧ s ≤ n`. -/
def IsTuranSystem (n s r : ℕ) (H : Finset (Finset (Fin n))) : Prop :=
  0 < r ∧ r < s ∧ s ≤ n ∧ SetFamily.IsUniform H r ∧
    ∀ T ∈ Finset.powersetCard s (Finset.univ : Finset (Fin n)), ∃ e ∈ H, e ⊆ T

/-- The complete `r`-graph: all `r`-subsets of `Fin n`. -/
def completeGraph (n r : ℕ) : Finset (Finset (Fin n)) :=
  Finset.powersetCard r (Finset.univ : Finset (Fin n))

/-- Realized sizes: cardinalities of Turan systems with parameters `n s r`. -/
def realizedCounts (n s r : ℕ) : Set ℕ :=
  { k | ∃ H, IsTuranSystem n s r H ∧ H.card = k }

/-- The Turan number: least realized size, `0` when no system exists. -/
noncomputable def turanNumber (n s r : ℕ) : ℕ := by
  classical
  exact if h : ∃ k, k ∈ realizedCounts n s r then Nat.find h else 0

end TuranSystem
