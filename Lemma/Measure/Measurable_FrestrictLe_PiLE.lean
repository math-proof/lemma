import Mathlib.Probability.Process.Filtration
import sympy.Basic
open MeasureTheory Preorder


@[main]
private lemma main
  {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
-- given
  (n : ℕ) :
-- imply
  Measurable[Filtration.piLE n] (frestrictLe (π := X) n) := by
-- proof
  rw [Filtration.piLE_eq_comap_frestrictLe]
  exact comap_measurable _


-- created on 2026-09-26