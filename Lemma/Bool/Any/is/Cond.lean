import Lemma.Bool.Cond.of.Any
import Lemma.Bool.Any.of.Cond
open Bool


@[main]
private lemma main
  [Inhabited α]:
-- imply
  (∃ _ : α, r) ↔ r :=
-- proof
  ⟨Cond.of.Any, Any.of.Cond (a := default)⟩


-- created on 2024-07-01
