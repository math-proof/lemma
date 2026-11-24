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
public import Theorem.GameTheory.SocialChoice.GibbardSatterthwaite.Part4


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/SocialChoice/GibbardSatterthwaite.lean -/
section

namespace MathlibExt.GameTheory.SocialChoice.GibbardSatterthwaiteWanted

/-- The induced social welfare function. -/
def socOrder {Alt Voter : Type*} [Fintype Alt] [DecidableEq Alt]
    [Fintype Voter] [DecidableEq Voter]
    (F : SocialChoiceFunction Alt Voter) (hSP : IsStrategyProof F) (hOnto : IsOnto F)
    (R : Profile Alt Voter) : StrictTotalOrder Alt where
  lt := socLT F R
  irrefl := fun _a h => h.1 rfl
  trans := fun hab hbc => socTrans F hSP hOnto R hab hbc
  total := fun hne => socTotal F hSP hOnto R hne

end MathlibExt.GameTheory.SocialChoice.GibbardSatterthwaiteWanted
end
