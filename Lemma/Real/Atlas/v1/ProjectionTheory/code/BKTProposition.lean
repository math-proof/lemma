import Mathlib
import Initialize.Tactic.Attr.Basic
open Pointwise


namespace BKTProof

/--
[card_sq_mul_card_sq_le_card_add_mul_addEnergy](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/BKTProposition.lean)
-/
@[path]
lemma card_sq_mul_card_sq_le_card_add_mul_addEnergy
  [DecidableEq α]
  [Add α]
  {A B : Finset α} :
-- imply
  A.card ^ 2 * B.card ^ 2 ≤ (A + B).card * A.addEnergy B :=
-- proof
  Finset.le_card_add_mul_addEnergy A B

end BKTProof


-- created on 2026-10-23
