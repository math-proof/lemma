import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraNotes.code.GroupActions
open GroupActions
open MulAction


namespace Definitions
end Definitions
namespace GroupActions

/--
[card_eq_sum_orbit_sizes](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/GroupActions.lean)
-/
@[path]
private lemma card_eq_sum_orbit_sizes
  [Group G]
  [MulAction G α]
  [Fintype α]
  [Fintype (orbitRel.Quotient G α)]
  [∀ ω : orbitRel.Quotient G α, Fintype ω.orbit] :
-- imply
  Fintype.card α = ∑ ω : orbitRel.Quotient G α, Fintype.card ω.orbit := by
-- proof
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr (selfEquivSigmaOrbits' G α)

end GroupActions

namespace GroupActions

/--
[card_orbit_eq_index_stabilizer](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/GroupActions.lean)
-/
@[path]
private lemma card_orbit_eq_index_stabilizer
  [Group G]
  [MulAction G α]
  {s : α} :
-- imply
  (stabilizer G s).index = (orbit G s).ncard :=
-- proof
  MulAction.index_stabilizer G s

end GroupActions


-- created on 2026-10-24
