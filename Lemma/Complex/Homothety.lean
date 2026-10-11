import Mathlib
import sympy.Basic
import sympy.functions.special.elliptic.Homothety
open PeriodPair


/--
[Homothety](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Elliptic/Homothety.lean)
-/
@[path]
private lemma is_homothetic_refl_is
-- given
  (L : PeriodPair) :
-- imply
  IsHomothetic L L := by
-- proof
  apply PeriodPair.IsHomothetic.refl L

/--
[Homothety](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Elliptic/Homothety.lean)
-/
@[path]
private lemma is_homothetic_symm_is
-- given
  (L L' : PeriodPair)
  (h : IsHomothetic L L') :
-- imply
  IsHomothetic L' L := by
-- proof
  apply PeriodPair.IsHomothetic.symm h

/--
[Homothety](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Elliptic/Homothety.lean)
-/
@[path]
private lemma is_homothetic_trans_is
-- given
  (L₁ L₂ L₃ : PeriodPair)
  (h₁₂ : IsHomothetic L₁ L₂)
  (h₂₃ : IsHomothetic L₂ L₃) :
-- imply
  IsHomothetic L₁ L₃ := by
-- proof
  apply PeriodPair.IsHomothetic.trans h₁₂ h₂₃

/--
[Homothety](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Elliptic/Homothety.lean)
-/
@[path]
private lemma is_homothetic_equivalence_is :
-- imply
  Equivalence IsHomothetic := by
-- proof
  apply PeriodPair.isHomothetic_equivalence


-- created on 2026-10-11
