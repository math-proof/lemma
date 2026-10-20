import Mathlib
import sympy.Basic
import sympy.atlas.GameTheory.SocialChoice.GibbardSatterthwaite
open MathlibExt.GameTheory.SocialChoice.GibbardSatterthwaiteWanted


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

/--
[gibbard_satterthwaite](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/SocialChoice/GibbardSatterthwaite.lean)
-/
@[path]
private lemma gibbard_satterthwaite_eq
  [Fintype Alt] [DecidableEq Alt] [Fintype Voter] [DecidableEq Voter] [Nonempty Voter]
  {F : SocialChoiceFunction Alt Voter}
-- given
  (hAlt : ∃ a b c : Alt, a ≠ b ∧ a ≠ c ∧ b ≠ c)
  (hOnto : IsOnto F)
  (hSP : IsStrategyProof F) :
-- imply
  IsDictatorial F := by
-- proof
  apply MathlibExt.GameTheory.SocialChoice.GibbardSatterthwaiteWanted.gibbard_satterthwaite hAlt F hOnto hSP


-- created on 2026-10-20
