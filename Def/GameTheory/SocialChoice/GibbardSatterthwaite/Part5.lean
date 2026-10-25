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
import Theorem.GameTheory.SocialChoice.GibbardSatterthwaite.Part4


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
