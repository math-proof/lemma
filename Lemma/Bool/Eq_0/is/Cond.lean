import Lemma.Bool.Cond.of.Eq_0
import Lemma.Bool.Eq_0.of.Cond
open Bool


@[main]
private lemma invert
  [Decidable p] :
-- imply
  Bool.toNat p = 0 ↔ ¬p :=
-- proof
  ⟨Cond.of.Eq_0.invert, Eq_0.of.Cond.invert.given⟩


-- created on 2026-09-27
