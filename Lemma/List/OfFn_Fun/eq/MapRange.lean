import sympy.concrete.continued_fraction
import sympy.Basic
open Continuant


@[main]
private lemma main
-- given
  (x : ℕ → R)
  (n : ℕ) :
-- imply
  List.ofFn (fun i : Fin n => x i) = (List.range n).map x := by
-- proof
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ', List.concat_eq_append, List.range_succ, List.map_append, ← ih]
    rfl


-- created on 2026-10-07
