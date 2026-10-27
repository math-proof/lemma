import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.ShermanFactor
open StatMech StatMech.Onsager


/--
[ons_factorTupleSum_eq_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanFactor.lean)
-/
@[path]
private lemma ons_factorTupleSum_eq_pow_eq
  [DecidableEq α]
  {S : Finset α}
  {wt : α → ℂ}
  {k : ℕ} :
-- imply
  (∑ p ∈ Fintype.piFinset (fun _ : Fin k => S), ∏ i : Fin k, wt (p i)) = (∑ s ∈ S, wt s) ^ k := by
-- proof
  apply StatMech.Onsager.ons_factorTupleSum_eq_pow S wt k

/--
[ons_tupleProd_eq_listProd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanFactor.lean)
-/
@[path]
private lemma ons_tupleProd_eq_listProd_eq
  [DecidableEq α]
  {wt : α → ℂ}
  {k : ℕ}
  {p : Fin k → α} :
-- imply
  ∏ i : Fin k, wt (p i) = ((List.ofFn p).map wt).prod := by
-- proof
  apply StatMech.Onsager.ons_tupleProd_eq_listProd wt p

/--
[ons_pow_eq_sum_list](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanFactor.lean)
-/
@[path]
private lemma ons_pow_eq_sum_list_eq
  [DecidableEq α]
  {S : Finset α}
  {wt : α → ℂ}
  {k : ℕ} :
-- imply
  (∑ s ∈ S, wt s) ^ k = ∑ L ∈ (Fintype.piFinset (fun _ : Fin k => S)).image (fun p => List.ofFn p), (L.map wt).prod := by
-- proof
  apply StatMech.Onsager.ons_pow_eq_sum_list S wt k

/--
[ons_factor_hcount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanFactor.lean)
-/
@[path]
private lemma ons_factor_hcount_eq
  [DecidableEq α]
  {S : Finset α}
  {wt : α → ℂ}
  {k : ℕ} :
-- imply
  (∑ p ∈ Fintype.piFinset (fun _ : Fin (k + 1) => S), ∏ i : Fin (k + 1), wt (p i)) = (∑ s ∈ S, wt s) ^ (k + 1) := by
-- proof
  apply StatMech.Onsager.ons_factor_hcount S wt k

/--
[ons_lemma4_factorized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanFactor.lean)
-/
@[path]
private lemma ons_lemma4_factorized_eq
  [DecidableEq α]
  {S : Finset α}
  {wt : α → ℂ}
-- given
  (hz : ‖∑ s ∈ S, wt s‖ < 1) :
-- imply
  (∑' k : ℕ, (∑ p ∈ Fintype.piFinset (fun _ : Fin (k + 1) => S), ∏ i : Fin (k + 1), wt (p i)) / (k + 1)) = -Complex.log (1 - ∑ s ∈ S, wt s) ∧ Complex.exp (-(∑' k : ℕ, (∑ p ∈ Fintype.piFinset (fun _ : Fin (k + 1) => S), ∏ i : Fin (k + 1), wt (p i)) / (k + 1))) = 1 - ∑ s ∈ S, wt s := by
-- proof
  apply StatMech.Onsager.ons_lemma4_factorized S wt hz


-- created on 2026-10-23
