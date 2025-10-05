import Lemma.Hyperreal.ExpSMul.eq.PowExp
open Hyperreal


@[main]
private lemma main
-- given
  (x : ℝ*)
  (n : ℕ) :
-- imply
  (n * x).exp = x.exp ^ n := by
-- proof
  simp [PowExp.eq.ExpSMul]


-- created on 2025-10-05
