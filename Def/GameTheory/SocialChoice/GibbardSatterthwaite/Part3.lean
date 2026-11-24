module
public import Mathlib.Data.Fintype.Basic
public import Instance.Order.StrictTotalOrder
public import Theorem.Set.StrictTotalOrder
public import Theorem.Set.SocialChoice.Arrow
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Tactic.Push
public import Def.GameTheory.SocialChoice.Arrow.Part3
public import Theorem.GameTheory.SocialChoice.GibbardSatterthwaite.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/SocialChoice/GibbardSatterthwaite.lean -/
section

namespace MathlibExt.GameTheory.SocialChoice.GibbardSatterthwaiteWanted

/-- Raise the pair `{a, b}` to the top of every voter's order. -/
def raisePair {Alt Voter : Type*} [DecidableEq Alt]
    (R : Profile Alt Voter) (a b : Alt) : Profile Alt Voter :=
  fun i => raiseOrder (R i) {a, b}

end MathlibExt.GameTheory.SocialChoice.GibbardSatterthwaiteWanted
end
