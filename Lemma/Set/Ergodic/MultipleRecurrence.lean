import Mathlib
import sympy.Basic
import sympy.atlas.Dynamics.Ergodic.MultipleRecurrence
open MeasureTheory
open scoped ENNReal
open MathlibExt.Dynamics.Ergodic.MultipleRecurrenceWanted


/--
[furstenberg_multipleRecurrence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Dynamics/Ergodic/MultipleRecurrence.lean)
-/
@[path]
private lemma furstenberg_multipleRecurrence_eq
  [MeasurableSpace α]
  {μ : Measure α} [IsProbabilityMeasure μ]
  {T : α → α}
  {A : Set α}
  {k : ℕ}
-- given
  (hT : MeasurePreserving T μ μ)
  (hA : MeasurableSet A)
  (hApos : 0 < μ A)
  (hk : 0 < k) :
-- imply
  ∃ n : ℕ, 0 < n ∧ 0 < μ (⋂ i ∈ Finset.range k, T^[i * n] ⁻¹' A) := by
-- proof
  apply MathlibExt.Dynamics.Ergodic.MultipleRecurrenceWanted.furstenberg_multipleRecurrence hT hA hApos k hk


-- created on 2026-10-20
