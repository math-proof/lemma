import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.ExchangeConditionProof
open CoxeterGroup CoxeterExchangeGenuine CoxeterExchange


namespace Definitions
end Definitions
namespace CoxeterExchange

/--
[exchange_implies_deletion](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/ExchangeConditionProof.lean)
-/
@[path]
private lemma exchange_implies_deletion
  [DecidableEq B]
  [Fintype B]
-- given
  (hsce : SignChangeExchangeHyp M cs) :
-- imply
  SatisfiesDeletionCondition M cs :=
-- proof
  deletion_of_exchange cs (exchange_condition_from_neg_of_descent M cs hsce)

end CoxeterExchange

namespace CoxeterExchange

/--
[exchange_implies_corollary](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/ExchangeConditionProof.lean)
-/
@[path]
private lemma exchange_implies_corollary
  [DecidableEq B]
  [Fintype B]
-- given
  (hsce : SignChangeExchangeHyp M cs) :
-- imply
  ExchangeCorollary M cs :=
-- proof
  corollary_of_exchange cs (exchange_condition_from_neg_of_descent M cs hsce)

end CoxeterExchange

namespace CoxeterExchange

/--
[exchange_implies_both](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/ExchangeConditionProof.lean)
-/
@[path]
private lemma exchange_implies_both
  [DecidableEq B]
  [Fintype B]
-- given
  (hsce : SignChangeExchangeHyp M cs) :
-- imply
  SatisfiesDeletionCondition M cs ∧ ExchangeCorollary M cs :=
-- proof
  let hex := exchange_condition_from_neg_of_descent M cs hsce
  ⟨deletion_of_exchange cs hex, corollary_of_exchange cs hex⟩

end CoxeterExchange


-- created on 2026-10-24
