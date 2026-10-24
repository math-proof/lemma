import Mathlib
import Lemma.List.Any_And_Eq_WordProd.of.Eq_WordProd.IsReduced.BruhatLE.ReducedSublistProperty.StrongExchangeCondition
open StrongExchangeUnconditional


/--
[bruhat_chain_property_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BruhatChainUnconditional.lean)
-/
@[path]
private lemma main
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {v w : M.Group}
-- given
  (hSEC_full : StrongExchangeCondition M.toCoxeterSystem)
  (hRSP : ReducedSublistProperty M.toCoxeterSystem)
  (hvw : BruhatLT M.toCoxeterSystem v w) :
-- imply
  ∃ (n : ℕ) (f : Fin (n + 2) → M.Group), f ⟨0, by omega⟩ = v ∧ f ⟨n + 1, by omega⟩ = w ∧ ∀ (i : Fin (n + 1)), BruhatLT M.toCoxeterSystem (f ⟨i.val, by omega⟩) (f ⟨i.val + 1, by omega⟩) ∧ M.toCoxeterSystem.length (f ⟨i.val, by omega⟩) + 1 = M.toCoxeterSystem.length (f ⟨i.val + 1, by omega⟩) :=
-- proof
  bruhat_chain_property M.toCoxeterSystem
    hSEC_full hRSP (strongExchangeForBruhat_unconditional M)
    hvw



-- created on 2026-10-23
-- updated on 2026-10-24
