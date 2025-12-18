import Lemma.Hyperreal.Infinite.of.Infinite.StDiv.ne.Zero
import Lemma.Hyperreal.Infinitesimal.of.Infinitesimal.StDiv.ne.Zero
import Lemma.Hyperreal.Ne_0.of.Infinite
import Lemma.Hyperreal.Ne_0.of.NotInfinitesimal
open Hyperreal


@[main]
private lemma main
  {a b : ℝ*}
-- given
  (h_st : st (a / b) = 1)
  (h_a : ¬a.Infinitesimal) :
-- imply
  a ≠ 0 ∧ b ≠ 0 := by
-- proof
  if h_a_inf : a.Infinite then
    have h_b_inf := Infinite.of.Infinite.StDiv.ne.Zero.left (by linarith) h_a_inf (b := b)
    exact ⟨Ne_0.of.Infinite h_a_inf, Ne_0.of.Infinite h_b_inf⟩
  else
    have h_b := NotInfinitesimal.of.NotInfinitesimal.StDiv.ne.Zero (by linarith) h_a (b := b)
    exact ⟨Ne_0.of.NotInfinitesimal h_a, Ne_0.of.NotInfinitesimal h_b⟩


-- created on 2025-12-18
