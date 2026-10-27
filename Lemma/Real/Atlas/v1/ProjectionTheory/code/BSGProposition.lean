import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.ProjectionTheory.code.BSGProposition
open Pointwise Finset in BSG


namespace BSG

/--
[sum_fiber_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/BSGProposition.lean)
-/
@[path]
lemma sum_fiber_le
  [DecidableEq G]
  [AddCommGroup G]
  [Fintype G]
  {X : Finset (G × G)}
  {S : Finset G} :
-- imply
  ∑ s ∈ S, ((sumsetImage X ×ˢ (sumsetImage X ×ˢ sumsetImage X)).filter (fun t => t.1 - t.2.1 + t.2.2 = s)).card ≤ (sumsetImage X).card ^ 3 := by
-- proof
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  calc Finset.card _ ≤ (sumsetImage X ×ˢ (sumsetImage X ×ˢ sumsetImage X)).card :=
    Finset.card_filter_le _ _
    _ = (sumsetImage X).card ^ 3 := by
      simp [Finset.card_product, pow_succ, pow_zero, mul_comm]

end BSG

/--
[BSG.card_sq_mul_card_sq_le_card_add_mul_addEnergy](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/BSGProposition.lean)
-/
@[path]
lemma BSG.card_sq_mul_card_sq_le_card_add_mul_addEnergy
  [DecidableEq α]
  [Add α]
  {A B : Finset α} :
-- imply
  A.card ^ 2 * B.card ^ 2 ≤ (A + B).card * A.addEnergy B :=
-- proof
  Finset.le_card_add_mul_addEnergy A B


-- created on 2026-10-23
