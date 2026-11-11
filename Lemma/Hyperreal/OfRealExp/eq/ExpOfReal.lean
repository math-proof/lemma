import Instance.Analysis.SpecialFunctions.Exponential.Part5


@[path, comm]
private lemma main
-- given
  (x : ℝ) :
-- imply
  Hyperreal.ofReal (Exp.exp x) = Exp.exp (Hyperreal.ofReal x) := by
-- proof
  rfl


-- created on 2026-07-28
