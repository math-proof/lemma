import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval


/--
[injective_of_shrunk_nonempty](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {d : ℕ}
  {P P_nonempty : Finset (Box d)}
  {B' : (B : Box d) → B ∈ P_nonempty → Box d}
-- given
  (hP_nonempty_sub : P_nonempty ⊆ P)
  (hP_disj : (P : Set (Box d)).PairwiseDisjoint Box.toSet)
  (h_sub : ∀ B (hB : B ∈ P_nonempty), (B' B hB).toSet ⊆ B.toSet)
  (h_nonempty : ∀ B (hB : B ∈ P_nonempty), (B' B hB).toSet.Nonempty) :
-- imply
  Function.Injective (fun x : { B // B ∈ P_nonempty } => B' x.1 x.2) :=
-- proof
  injective_of_shrunk_nonempty hP_nonempty_sub hP_disj h_sub h_nonempty


-- created on 2026-10-22
