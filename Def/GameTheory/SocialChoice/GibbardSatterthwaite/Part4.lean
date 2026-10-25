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
import Theorem.GameTheory.SocialChoice.GibbardSatterthwaite.Part3


section

namespace MathlibExt.GameTheory.SocialChoice.GibbardSatterthwaiteWanted

/-- Induced social relation: `a` is socially above `b` if `a ≠ b` and `F`
picks `a` when `{a, b}` is raised to the top everywhere. -/
def socLT {Alt Voter : Type*} [DecidableEq Alt]
    (F : SocialChoiceFunction Alt Voter) (R : Profile Alt Voter) (a b : Alt) : Prop :=
  a ≠ b ∧ F (raisePair R a b) = a

end MathlibExt.GameTheory.SocialChoice.GibbardSatterthwaiteWanted
end
