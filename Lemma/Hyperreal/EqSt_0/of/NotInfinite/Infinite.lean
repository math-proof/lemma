import Lemma.Hyperreal.EqSt_0.of.Infinitesimal
import Lemma.Hyperreal.InfinitesimalDiv.of.NotInfinite.Infinite
open Hyperreal


/--
the hypotheses are arranged in the constructor order of division a / b
-/
@[main, mt 1]
private lemma main
  {a : ℝ*}
-- given
  (h_a : ¬a → ∞)
  (h_b : b → ∞) :
-- imply
  stdPart (a / b) = 0 := by
-- proof
  apply EqSt_0.of.Infinitesimal
  apply InfinitesimalDiv.of.NotInfinite.Infinite h_a h_b


-- created on 2026-07-25
