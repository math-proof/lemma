import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.SpecialFunctions.Part1Ch7DirichletBeta

open Ramanujan.Part1Ch7.DirichletBeta


namespace MathlibExt.Analysis.Ramanujan.Part1Ch7.DirichletBeta

/--
[Part1Ch7DirichletBeta](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7DirichletBeta.lean)
-/
@[path]
private lemma betaCharOdd_eq :
-- imply
  ∀ a : ZMod 4, chapter7BetaCharacter (-a) = -chapter7BetaCharacter a :=
-- proof
  betaCharOdd

end MathlibExt.Analysis.Ramanujan.Part1Ch7.DirichletBeta

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7.DirichletBeta

/--
[Part1Ch7DirichletBeta](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7DirichletBeta.lean)
-/
@[path]
private lemma betaCharUnivFour_eq :
-- imply
  (Finset.univ : Finset (ZMod 4)) = {0, 1, 2, 3} :=
-- proof
  betaCharUnivFour

end MathlibExt.Analysis.Ramanujan.Part1Ch7.DirichletBeta

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7.DirichletBeta

/--
[Part1Ch7DirichletBeta](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7DirichletBeta.lean)
-/
@[path]
private lemma betaCharSum_eq :
-- imply
  ∑ j : ZMod 4, chapter7BetaCharacter j = 0 :=
-- proof
  betaCharSum

end MathlibExt.Analysis.Ramanujan.Part1Ch7.DirichletBeta

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7.DirichletBeta

/--
[Part1Ch7DirichletBeta](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7DirichletBeta.lean)
-/
@[path]
private lemma betaDirichletEntire_eq :
-- imply
  Differentiable ℂ chapter7DirichletBeta :=
-- proof
  betaDirichletEntire

end MathlibExt.Analysis.Ramanujan.Part1Ch7.DirichletBeta

/--
[Part1Ch7DirichletBeta](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7DirichletBeta.lean)
-/
@[path]
private lemma beta_char0_eq :
-- imply
  chapter7BetaCharacter 0 = 0 :=
-- proof
  Ramanujan.Part1Ch7.DirichletBeta.betaChar0

/--
[Part1Ch7DirichletBeta](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7DirichletBeta.lean)
-/
@[path]
private lemma beta_char1_eq :
-- imply
  chapter7BetaCharacter 1 = 1 :=
-- proof
  Ramanujan.Part1Ch7.DirichletBeta.betaChar1

/--
[Part1Ch7DirichletBeta](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7DirichletBeta.lean)
-/
@[path]
private lemma beta_char2_eq :
-- imply
  chapter7BetaCharacter 2 = 0 :=
-- proof
  Ramanujan.Part1Ch7.DirichletBeta.betaChar2

/--
[Part1Ch7DirichletBeta](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7DirichletBeta.lean)
-/
@[path]
private lemma beta_char3_eq :
-- imply
  chapter7BetaCharacter 3 = -1 :=
-- proof
  Ramanujan.Part1Ch7.DirichletBeta.betaChar3


-- created on 2026-10-10
-- updated on 2026-10-26
