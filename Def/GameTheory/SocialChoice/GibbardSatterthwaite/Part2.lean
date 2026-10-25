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
import Theorem.GameTheory.SocialChoice.GibbardSatterthwaite


section

namespace MathlibExt.GameTheory.SocialChoice.GibbardSatterthwaiteWanted

-- Step 2: raising a set to the top, unanimity, weak Pareto.

/-- Raise the set `P` to the top of `o`, keeping the internal order inside
and outside `P`. -/
def raiseOrder {Alt : Type*} [DecidableEq Alt] (o : StrictTotalOrder Alt)
    (P : Finset Alt) : StrictTotalOrder Alt where
  lt := fun x y =>
    (x ∈ P ∧ y ∉ P) ∨ (((x ∈ P ∧ y ∈ P) ∨ (x ∉ P ∧ y ∉ P)) ∧ o.lt x y)
  irrefl := by
    intro a h
    rcases h with ⟨ha, hna⟩ | ⟨_, hlt⟩
    · exact hna ha
    · exact o.irrefl a hlt
  trans := by
    intro a b c hab hbc
    rcases hab with ⟨haP, hnbP⟩ | ⟨hsab, hltab⟩
    · rcases hbc with ⟨hbP, hncP⟩ | ⟨hsbc, _⟩
      · exact absurd hbP hnbP
      · rcases hsbc with ⟨hbP, hcP⟩ | ⟨hnbP, hncP⟩
        · exact absurd hbP hnbP
        · exact Or.inl ⟨haP, hncP⟩
    · rcases hbc with ⟨hbP, hncP⟩ | ⟨hsbc, hltbc⟩
      · rcases hsab with ⟨haP, _⟩ | ⟨_, hnbP⟩
        · exact Or.inl ⟨haP, hncP⟩
        · exact absurd hbP hnbP
      · have hltac : o.lt a c := o.trans hltab hltbc
        rcases hsab with ⟨haP, hbP⟩ | ⟨hnaP, hnbP⟩
        · rcases hsbc with ⟨_, hcP⟩ | ⟨hnbP, _⟩
          · exact Or.inr ⟨Or.inl ⟨haP, hcP⟩, hltac⟩
          · exact absurd hbP hnbP
        · rcases hsbc with ⟨hbP, _⟩ | ⟨_, hncP⟩
          · exact absurd hbP hnbP
          · exact Or.inr ⟨Or.inr ⟨hnaP, hncP⟩, hltac⟩
  total := by
    intro a b hne
    by_cases haP : a ∈ P <;> by_cases hbP : b ∈ P
    · rcases o.total hne with h | h
      · exact Or.inl (Or.inr ⟨Or.inl ⟨haP, hbP⟩, h⟩)
      · exact Or.inr (Or.inr ⟨Or.inl ⟨hbP, haP⟩, h⟩)
    · exact Or.inl (Or.inl ⟨haP, hbP⟩)
    · exact Or.inr (Or.inl ⟨hbP, haP⟩)
    · rcases o.total hne with h | h
      · exact Or.inl (Or.inr ⟨Or.inr ⟨haP, hbP⟩, h⟩)
      · exact Or.inr (Or.inr ⟨Or.inr ⟨hbP, haP⟩, h⟩)

end MathlibExt.GameTheory.SocialChoice.GibbardSatterthwaiteWanted
end
