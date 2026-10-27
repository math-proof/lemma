import Mathlib
import Initialize.Tactic.Attr.Basic
open Finset BigOperators

/--
[prod_banach_space](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToFunctionalAnalysis/code/BanachSpace.lean)
-/
@[path]
lemma prod_banach_space
  {B₁ B₂ : Type*}
  [NormedAddCommGroup B₁]
  [NormedAddCommGroup B₂]
  [CompleteSpace B₁]
  [CompleteSpace B₂] :
-- imply
  CompleteSpace (WithLp 1 (B₁ × B₂)) :=
-- proof
  inferInstance
open Finset BigOperators

/--
[cauchySeq_of_summable_norm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToFunctionalAnalysis/code/BanachSpace.lean)
-/
@[path]
lemma cauchySeq_of_summable_norm
  [SeminormedAddCommGroup E]
  {v : ℕ → E}
-- given
  (hv : Summable fun n => ‖v n‖) :
-- imply
  CauchySeq fun m => ∑ i ∈ Finset.range m, v i :=
-- proof
  cauchySeq_range_of_norm_bounded (hv.hasSum.tendsto_sum_nat.cauchySeq) (fun _ => le_rfl)


-- created on 2026-10-23
-- updated on 2026-10-26
