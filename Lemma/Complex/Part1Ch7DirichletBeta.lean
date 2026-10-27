import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.SpecialFunctions.Part1Ch7DirichletBeta

open Ramanujan.Part1Ch7.DirichletBeta


namespace MathlibExt.Analysis.Ramanujan.Part1Ch7.DirichletBeta

/--
[Part1Ch7DirichletBeta](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7DirichletBeta.lean)
-/
@[path]
lemma betaCharOdd
-- imply
  ∀ a : ZMod 4, chapter7BetaCharacter (-a) = -chapter7BetaCharacter a := by
-- proof
  have h4 : ∀ a : ZMod 4, a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 := by decide
  have n1 : (-1 : ZMod 4) = 3 := by decide
  have n2 : (-2 : ZMod 4) = 2 := by decide
  have n3 : (-3 : ZMod 4) = 1 := by decide
  intro a
  obtain rfl | rfl | rfl | rfl <;> := h4 a
    simp [betaChar0, betaChar1, betaChar2, betaChar3, n1, n2, n3]

end MathlibExt.Analysis.Ramanujan.Part1Ch7.DirichletBeta

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7.DirichletBeta

/--
[Part1Ch7DirichletBeta](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7DirichletBeta.lean)
-/
@[path]
lemma betaCharUnivFour
-- imply
  (Finset.univ : Finset (ZMod 4)) = {0, 1, 2, 3} := by
-- proof
decide

end MathlibExt.Analysis.Ramanujan.Part1Ch7.DirichletBeta

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7.DirichletBeta

/--
[Part1Ch7DirichletBeta](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7DirichletBeta.lean)
-/
@[path]
lemma betaCharSum
-- imply
  ∑ j : ZMod 4, chapter7BetaCharacter j = 0 := by
-- proof
  rw [betaCharUnivFour, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton, betaChar0, betaChar1, betaChar2,
    betaChar3]
  ring

end MathlibExt.Analysis.Ramanujan.Part1Ch7.DirichletBeta

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7.DirichletBeta

/--
[Part1Ch7DirichletBeta](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7DirichletBeta.lean)
-/
@[path]
lemma betaDirichletEntire
-- imply
  Differentiable ℂ chapter7DirichletBeta := by
-- proof
  have hNe : NeZero 4 := ⟨by decide⟩
  intro s
  exact ZMod.differentiableAt_LFunction _ s (Or.inr betaCharSum)
end


/--
[Part1Ch7DirichletBeta](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7DirichletBeta.lean)
-/
@[path]
private lemma beta_char0_eq :
-- imply
  chapter7BetaCharacter 0 = 0 := by
-- proof
  apply Ramanujan.Part1Ch7.DirichletBeta.betaChar0

/--
[Part1Ch7DirichletBeta](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7DirichletBeta.lean)
-/
@[path]
private lemma beta_char1_eq :
-- imply
  chapter7BetaCharacter 1 = 1 := by
-- proof
  apply Ramanujan.Part1Ch7.DirichletBeta.betaChar1

/--
[Part1Ch7DirichletBeta](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7DirichletBeta.lean)
-/
@[path]
private lemma beta_char2_eq :
-- imply
  chapter7BetaCharacter 2 = 0 := by
-- proof
  apply Ramanujan.Part1Ch7.DirichletBeta.betaChar2

/--
[Part1Ch7DirichletBeta](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7DirichletBeta.lean)
-/
@[path]
private lemma beta_char3_eq :
-- imply
  chapter7BetaCharacter 3 = -1 := by
-- proof
  apply Ramanujan.Part1Ch7.DirichletBeta.betaChar3


-- created on 2026-10-10
-- updated on 2026-10-26
