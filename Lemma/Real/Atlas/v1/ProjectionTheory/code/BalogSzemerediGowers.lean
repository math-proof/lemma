import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.ProjectionTheory.code.KeyLemmaBSG
import Lemma.Real.Atlas.v1.ProjectionTheory.code.KeyLemmaBSG
open Finset Pointwise


namespace BalogSzemerediGowers

/--
[sum_fiber_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/BalogSzemerediGowers.lean)
-/
@[path]
lemma sum_fiber_le
  [DecidableEq G]
  [AddCommGroup G]
  {X : Finset (G × G)}
  {S : Finset G} :
-- imply
  ∑ s ∈ S, (((X.image (fun p => p.1 + p.2)) ×ˢ ((X.image (fun p => p.1 + p.2)) ×ˢ (X.image (fun p => p.1 + p.2)))).filter (fun t => t.1 - t.2.1 + t.2.2 = s)).card ≤ (X.image (fun p => p.1 + p.2)).card ^ 3 := by
-- proof
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  calc Finset.card _ ≤ ((X.image (fun p => p.1 + p.2)) ×ˢ
    ((X.image (fun p => p.1 + p.2)) ×ˢ (X.image (fun p => p.1 + p.2)))).card :=
      Finset.card_filter_le _ _
    _ = (X.image (fun p => p.1 + p.2)).card ^ 3 := by
      simp [Finset.card_product, pow_succ, pow_zero, mul_comm]

end BalogSzemerediGowers


-- created on 2026-10-23
