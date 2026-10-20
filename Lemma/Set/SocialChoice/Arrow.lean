import Mathlib
import sympy.Basic
import sympy.atlas.GameTheory.SocialChoice.Arrow
open MathlibExt.GameTheory.SocialChoice.ArrowWanted


/--
[arrow_impossibility_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/SocialChoice/Arrow.lean)
-/
@[path]
private lemma arrow_impossibility_general_eq
  [Finite Alt] [Finite Voter] [Nonempty Voter]
  {F : SocialWelfareFunction Alt Voter}
-- given
  (hAlt : ∃ a b c : Alt, a ≠ b ∧ a ≠ c ∧ b ≠ c)
  (hPareto : IsPareto F)
  (hIIA : IsIIA F) :
-- imply
  IsDictatorial F := by
-- proof
  apply MathlibExt.GameTheory.SocialChoice.ArrowWanted.arrow_impossibility_general hAlt F hPareto hIIA

/--
[arrow_impossibility](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/SocialChoice/Arrow.lean)
-/
@[path]
private lemma arrow_impossibility_eq
  [Fintype Alt] [DecidableEq Alt] [Fintype Voter] [DecidableEq Voter] [Nonempty Voter]
  {F : SocialWelfareFunction Alt Voter}
-- given
  (hAlt : ∃ a b c : Alt, a ≠ b ∧ a ≠ c ∧ b ≠ c)
  (hPareto : IsPareto F)
  (hIIA : IsIIA F) :
-- imply
  IsDictatorial F := by
-- proof
  apply MathlibExt.GameTheory.SocialChoice.ArrowWanted.arrow_impossibility hAlt F hPareto hIIA


-- created on 2026-10-20
