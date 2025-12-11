import Lemma.Hyperreal.InfinitesimalMul.of.Infinitesimal.Infinitesimal
open Hyperreal


@[main]
private lemma main
  [NeZero (n : ℕ)]
  {x : ℝ*}
-- given
  (h : Infinitesimal x) :
-- imply
  Infinitesimal (x ^ n) := by
-- proof
  have h_n := NeZero.ne n
  induction n generalizing x with
  | zero =>
    contradiction
  | succ n ih =>
    if h_n : n = 0 then
      subst h_n
      simpa
    else
      have ih := ih h h_n
      have := InfinitesimalMul.of.Infinitesimal.Infinitesimal h ih
      grind


-- created on 2025-12-11
