import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_2_1
open BoundedInterval


/--
[card_ratio_bound](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {P_nonempty P : Finset α}
  {δ : ℝ}
-- given
  (hP_nonempty_sub : P_nonempty ⊆ P)
  (hδ_pos : 0 < δ)
  (hcard_pos : 0 < P.card) :
-- imply
  P_nonempty.card * (δ / (4 * P.card)) ≤ δ / 4 :=
-- proof
  card_ratio_bound hP_nonempty_sub hδ_pos hcard_pos


-- created on 2026-10-22
