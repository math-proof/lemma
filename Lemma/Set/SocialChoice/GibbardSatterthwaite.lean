import Mathlib
import sympy.Basic
import Theorem.GameTheory.SocialChoice.GibbardSatterthwaite.Part5
open MathlibExt.GameTheory.SocialChoice.GibbardSatterthwaiteWanted


namespace MathlibExt.GameTheory.SocialChoice.GibbardSatterthwaiteWanted

/--
[sto_ne_of_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/SocialChoice/GibbardSatterthwaite.lean)
-/
@[path]
private lemma sto_ne_of_lt {Alt : Type*} (o : StrictTotalOrder Alt) {a b : Alt}
  (h : o.lt a b) : a ≠ b :=
  fun heq => o.irrefl a (heq ▸ h)

end MathlibExt.GameTheory.SocialChoice.GibbardSatterthwaiteWanted

namespace MathlibExt.GameTheory.SocialChoice.GibbardSatterthwaiteWanted

/--
[sto_gt_of_not_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/SocialChoice/GibbardSatterthwaite.lean)
-/
@[path]
private lemma sto_gt_of_not_lt {Alt : Type*} (o : StrictTotalOrder Alt) {a b : Alt}
  (hne : a ≠ b) (h : ¬ o.lt a b) : o.lt b a := by
  obtain h1 | h1 := o.total hne
  · exact absurd h1 h
  · exact h1

end MathlibExt.GameTheory.SocialChoice.GibbardSatterthwaiteWanted

namespace MathlibExt.GameTheory.SocialChoice.GibbardSatterthwaiteWanted

/--
[third_alt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/SocialChoice/GibbardSatterthwaite.lean)
-/
@[path]
distinct from both. -/
private lemma third_alt {Alt : Type*}
  (hAlt : ∃ a b c : Alt, a ≠ b ∧ a ≠ c ∧ b ≠ c)
  (u v : Alt) : ∃ w : Alt, w ≠ u ∧ w ≠ v := by
  classical
  obtain ⟨a, b, c, hab, hac, hbc⟩ := hAlt
  by_contra hcon
  push Not at hcon
  have ha' : a = u ∨ a = v := by
    by_cases h : a = u
    · exact Or.inl h
    · exact Or.inr (hcon a h)
  have hb' : b = u ∨ b = v := by
    by_cases h : b = u
    · exact Or.inl h
    · exact Or.inr (hcon b h)
  have hc' : c = u ∨ c = v := by
    by_cases h : c = u
    · exact Or.inl h
    · exact Or.inr (hcon c h)
  obtain rfl | rfl <;> rcases hb' with rfl | rfl <;> rcases hc' with rfl | rfl <;> := ha'
    contradiction

end MathlibExt.GameTheory.SocialChoice.GibbardSatterthwaiteWanted

namespace MathlibExt.GameTheory.SocialChoice.GibbardSatterthwaiteWanted

/--
[exists_ne](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/SocialChoice/GibbardSatterthwaite.lean)
-/
@[path]
private lemma exists_ne {Alt : Type*}
  (hAlt : ∃ a b c : Alt, a ≠ b ∧ a ≠ c ∧ b ≠ c) (u : Alt) : ∃ w : Alt, w ≠ u := by
  classical
  obtain ⟨w, hw, _⟩ := third_alt hAlt u u
  exact ⟨w, hw⟩

end MathlibExt.GameTheory.SocialChoice.GibbardSatterthwaiteWanted

namespace MathlibExt.GameTheory.SocialChoice.GibbardSatterthwaiteWanted

/--
[gibbard_satterthwaite](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/SocialChoice/GibbardSatterthwaite.lean)
-/
@[path]
lemma gibbard_satterthwaite
  [Fintype Alt] [DecidableEq Alt] [Fintype Voter] [DecidableEq Voter] [Nonempty Voter]
  {F : SocialChoiceFunction Alt Voter}
-- given
  (hAlt : ∃ a b c : Alt, a ≠ b ∧ a ≠ c ∧ b ≠ c)
  (hOnto : IsOnto F)
  (hSP : IsStrategyProof F) :
-- imply
  IsDictatorial F :=
-- proof
  gibbard_satterthwaite_general hAlt F hOnto hSP
end MathlibExt.GameTheory.SocialChoice.GibbardSatterthwaiteWanted


/--
[gibbard_satterthwaite_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/SocialChoice/GibbardSatterthwaite.lean)
-/
@[path]
private lemma gibbard_satterthwaite_general_eq
  [Finite Alt] [Finite Voter] [Nonempty Voter]
  {F : SocialChoiceFunction Alt Voter}
-- given
  (hAlt : ∃ a b c : Alt, a ≠ b ∧ a ≠ c ∧ b ≠ c)
  (hOnto : IsOnto F)
  (hSP : IsStrategyProof F) :
-- imply
  IsDictatorial F := by
-- proof
  apply MathlibExt.GameTheory.SocialChoice.GibbardSatterthwaiteWanted.gibbard_satterthwaite_general hAlt F hOnto hSP


-- created on 2026-10-20
-- updated on 2026-10-23
