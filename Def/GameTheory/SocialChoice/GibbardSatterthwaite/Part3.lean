/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/SocialChoice/GibbardSatterthwaite.lean -/

import Mathlib.Data.Fintype.Basic
import Instance.Order.StrictTotalOrder
import Lemma.Set.StrictTotalOrder
import Lemma.Set.SocialChoice.Arrow
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Push
import Def.GameTheory.SocialChoice.Arrow.Part3
import Theorem.GameTheory.SocialChoice.GibbardSatterthwaite.Part2


section

namespace MathlibExt.GameTheory.SocialChoice.GibbardSatterthwaiteWanted

/-- Raise the pair `{a, b}` to the top of every voter's order. -/
def raisePair {Alt Voter : Type*} [DecidableEq Alt]
    (R : Profile Alt Voter) (a b : Alt) : Profile Alt Voter :=
  fun i => raiseOrder (R i) {a, b}

end MathlibExt.GameTheory.SocialChoice.GibbardSatterthwaiteWanted
end
