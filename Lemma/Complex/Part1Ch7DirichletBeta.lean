import Mathlib
import sympy.Basic
import sympy.functions.special.ramanujan.Part1Ch7DirichletBeta

open Ramanujan.Part1Ch7.DirichletBeta

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

/--
[Part1Ch7DirichletBeta](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7DirichletBeta.lean)
-/
@[path]
private lemma beta_char_odd_eq :
-- imply
  ∀ a : ZMod 4, chapter7BetaCharacter (-a) = -chapter7BetaCharacter a := by
-- proof
  apply Ramanujan.Part1Ch7.DirichletBeta.betaCharOdd

/--
[Part1Ch7DirichletBeta](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7DirichletBeta.lean)
-/
@[path]
private lemma beta_char_univ_four_eq :
-- imply
  (Finset.univ : Finset (ZMod 4)) = {0, 1, 2, 3} := by
-- proof
  apply Ramanujan.Part1Ch7.DirichletBeta.betaCharUnivFour

/--
[Part1Ch7DirichletBeta](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7DirichletBeta.lean)
-/
@[path]
private lemma beta_char_sum_eq :
-- imply
  ∑ j : ZMod 4, chapter7BetaCharacter j = 0 := by
-- proof
  apply Ramanujan.Part1Ch7.DirichletBeta.betaCharSum

/--
[Part1Ch7DirichletBeta](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7DirichletBeta.lean)
-/
@[path]
private lemma beta_dirichlet_entire_is :
-- imply
  Differentiable ℂ chapter7DirichletBeta := by
-- proof
  apply Ramanujan.Part1Ch7.DirichletBeta.betaDirichletEntire

-- created on 2026-10-10
