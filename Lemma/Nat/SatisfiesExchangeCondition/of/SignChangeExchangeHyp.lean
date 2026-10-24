import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.CoxeterGroup.ExchangeConditionWiring
open CoxeterGroup CoxeterExchangeGenuine CoxeterExchange


namespace Definitions
end Definitions
namespace CoxeterExchange

/--
[exchange_condition_from_neg_of_descent](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/ExchangeConditionWiring.lean)
-/
@[path]
private lemma exchange_condition_from_neg_of_descent
  [DecidableEq B]
  [Fintype B]
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
-- given
  (hsce : SignChangeExchangeHyp M cs) :
-- imply
  SatisfiesExchangeCondition M cs :=
-- proof
  exchange_from_bridge (geometricBridgeFromNegOfDescent M cs hsce)

end CoxeterExchange


-- created on 2026-10-24
