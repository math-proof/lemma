/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/SocialChoice/Arrow.lean -/

import Mathlib.Data.Fintype.Basic
import Instance.Order.StrictTotalOrder
import Lemma.Set.StrictTotalOrder
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.SuccPred
import Abbrev.GameTheory.SocialChoice.Arrow


section

namespace MathlibExt.GameTheory.SocialChoice.ArrowWanted

/-- Pareto/unanimity: if every voter strictly prefers `a` to `b`, so does society. -/
def IsPareto {Alt Voter : Type*} (F : SocialWelfareFunction Alt Voter) : Prop :=
  ∀ (p : Profile Alt Voter) (a b : Alt), (∀ i, (p i).lt a b) → (F p).lt a b

/-- Independence of irrelevant alternatives: the social comparison of each pair `a,b`
depends only on voters' comparisons of that pair. That is, if two profiles agree on all
voters' `a`-vs-`b` comparisons, the social `a`-vs-`b` comparison agrees. -/
def IsIIA {Alt Voter : Type*} (F : SocialWelfareFunction Alt Voter) : Prop :=
  ∀ (p₁ p₂ : Profile Alt Voter) (a b : Alt),
    (∀ i, (p₁ i).lt a b ↔ (p₂ i).lt a b) → ((F p₁).lt a b ↔ (F p₂).lt a b)

/-- `d` is a dictator for `F`: the social order always extends `d`'s strict preferences. -/
def IsDictator {Alt Voter : Type*} (F : SocialWelfareFunction Alt Voter) (d : Voter) : Prop :=
  ∀ (p : Profile Alt Voter) (a b : Alt), (p d).lt a b → (F p).lt a b

/-- Dictatorship: some fixed voter whose strict preferences are always respected socially. -/
def IsDictatorial {Alt Voter : Type*} (F : SocialWelfareFunction Alt Voter) : Prop :=
  ∃ d : Voter, IsDictator F d

/-- An arbitrary injection from alternatives into naturals. -/
noncomputable def baseRank {Alt : Type*} [Fintype Alt] : Alt → ℕ :=
  fun w => (Fintype.equivFin Alt w).val

end MathlibExt.GameTheory.SocialChoice.ArrowWanted
end
