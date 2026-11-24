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
public import Theorem.GameTheory.SocialChoice.GibbardSatterthwaite.Part3


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/SocialChoice/GibbardSatterthwaite.lean -/
section

namespace MathlibExt.GameTheory.SocialChoice.GibbardSatterthwaiteWanted

/-- Induced social relation: `a` is socially above `b` if `a ≠ b` and `F`
picks `a` when `{a, b}` is raised to the top everywhere. -/
def socLT {Alt Voter : Type*} [DecidableEq Alt]
    (F : SocialChoiceFunction Alt Voter) (R : Profile Alt Voter) (a b : Alt) : Prop :=
  a ≠ b ∧ F (raisePair R a b) = a

end MathlibExt.GameTheory.SocialChoice.GibbardSatterthwaiteWanted
end
