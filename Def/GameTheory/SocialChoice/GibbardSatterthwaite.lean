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
import Abbrev.GameTheory.SocialChoice.GibbardSatterthwaite


section

namespace MathlibExt.GameTheory.SocialChoice.GibbardSatterthwaiteWanted

/-- `top` is top-ranked by `o` if it beats every other distinct alternative. -/
def IsTopRanked {Alt : Type*} (o : StrictTotalOrder Alt) (top : Alt) : Prop :=
  ∀ b, b ≠ top → o.lt top b

/-- Onto / surjective: every alternative is chosen for some profile. -/
def IsOnto {Alt Voter : Type*} (F : SocialChoiceFunction Alt Voter) : Prop :=
  ∀ a, ∃ p : Profile Alt Voter, F p = a

/-- `p₂` differs from `p₁` at most at voter `i`. -/
def DiffAtMostAt {Alt Voter : Type*} (p₁ p₂ : Profile Alt Voter) (i : Voter) : Prop :=
  ∀ j, j ≠ i → p₁ j = p₂ j

/-- Strategy-proof: no voter can get a strictly preferred outcome
(according to true ranking) by unilateral misreport. -/
def IsStrategyProof {Alt Voter : Type*} (F : SocialChoiceFunction Alt Voter) : Prop :=
  ∀ (p₁ : Profile Alt Voter) (i : Voter) (p₂ : Profile Alt Voter),
    DiffAtMostAt p₁ p₂ i → ¬ (p₁ i).lt (F p₂) (F p₁)

/-- `d` is a dictator: chosen outcome is always top-ranked by `d`. -/
def IsDictator {Alt Voter : Type*} (F : SocialChoiceFunction Alt Voter) (d : Voter) : Prop :=
  ∀ p : Profile Alt Voter, IsTopRanked (p d) (F p)

/-- Dictatorial SCF: some fixed voter always gets top choice. -/
def IsDictatorial {Alt Voter : Type*} (F : SocialChoiceFunction Alt Voter) : Prop :=
  ∃ d : Voter, IsDictator F d

end MathlibExt.GameTheory.SocialChoice.GibbardSatterthwaiteWanted
end
