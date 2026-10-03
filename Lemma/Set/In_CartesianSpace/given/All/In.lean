import sympy.Basic
import Lemma.Set.In_CartesianSpace.is.All.In


@[main]
private lemma main
  {n : ℕ}
  {x : Fin n → α}
  {S : Set α}
-- given
  (h : x ∈ Set.univ.pi (fun _ => S)) :
-- imply
  ∀ k, x k ∈ S := by
-- proof
  exact Set.In_CartesianSpace.is.All.In.mp h


-- created on 2026-10-03
