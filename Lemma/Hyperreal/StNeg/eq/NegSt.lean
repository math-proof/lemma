import Def.Analysis.Real.Limits.Basic
import Initialize.Tactic.Attr.Basic
open ArchimedeanClass


@[path]
private lemma main
-- given
  (x : ℝ*) :
-- imply
  stdPart (-x) = -stdPart x :=
-- proof
  ArchimedeanClass.stdPart_neg x


-- created on 2025-12-16
