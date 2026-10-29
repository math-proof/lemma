import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.MathlibExtTest.NumberTheory.ImaginaryQuadraticDiscriminant.Part2
open ImaginaryQuadraticDiscriminant


namespace ImaginaryQuadraticDiscriminant

/--
[mem_neg_three](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/ImaginaryQuadraticDiscriminant.lean)
-/
@[path]
lemma mem_neg_three :
-- imply
  IsImaginaryQuadraticDiscriminant (-3 : Int) := by
-- proof
  unfold IsImaginaryQuadraticDiscriminant
  decide

end ImaginaryQuadraticDiscriminant

namespace ImaginaryQuadraticDiscriminant

/--
[not_fund_neg_twelve_canonical](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/ImaginaryQuadraticDiscriminant.lean)
-/
@[path]
lemma not_fund_neg_twelve_canonical :
-- imply
  ¬ MetaMathlibExt.IsFundamentalDiscriminant (-12 : Int) := by
-- proof
  unfold MetaMathlibExt.IsFundamentalDiscriminant
  rintro (⟨_, hmod⟩ | ⟨m, hDm, _, hmodm⟩)
  · omega
  · have hm : m = -3 := by omega
    subst hm
    omega

end ImaginaryQuadraticDiscriminant

/--
[mem_neg_four](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/ImaginaryQuadraticDiscriminant.lean)
-/
@[path]
lemma mem_neg_four :
-- imply
  IsImaginaryQuadraticDiscriminant (-4 : Int) := by
-- proof
  unfold IsImaginaryQuadraticDiscriminant
  decide


namespace ImaginaryQuadraticDiscriminant

/--
[not_mem_neg_five](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/ImaginaryQuadraticDiscriminant.lean)
-/
@[path]
lemma not_mem_neg_five :
-- imply
  ¬ IsImaginaryQuadraticDiscriminant (-5 : Int) := by
-- proof
  unfold IsImaginaryQuadraticDiscriminant
  decide

end ImaginaryQuadraticDiscriminant

namespace ImaginaryQuadraticDiscriminant

/--
[not_mem_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/ImaginaryQuadraticDiscriminant.lean)
-/
@[path]
lemma not_mem_zero :
-- imply
  ¬ IsImaginaryQuadraticDiscriminant (0 : Int) := by
-- proof
  unfold IsImaginaryQuadraticDiscriminant
  decide

end ImaginaryQuadraticDiscriminant

namespace ImaginaryQuadraticDiscriminant

/--
[mem_neg_twelve](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/ImaginaryQuadraticDiscriminant.lean)
-/
@[path]
lemma mem_neg_twelve :
-- imply
  IsImaginaryQuadraticDiscriminant (-12 : Int) := by
-- proof
  unfold IsImaginaryQuadraticDiscriminant
  decide

end ImaginaryQuadraticDiscriminant

/--
[fund_neg_three_canonical](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/ImaginaryQuadraticDiscriminant.lean)
-/
@[path]
private lemma fund_neg_three_canonical_eq :
-- imply
  MetaMathlibExt.IsFundamentalDiscriminant (-3 : Int) := by
-- proof
  apply ImaginaryQuadraticDiscriminant.fund_neg_three_canonical

/--
[fund_neg_three](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/ImaginaryQuadraticDiscriminant.lean)
-/
@[path]
private lemma fund_neg_three_eq :
-- imply
  IsFundamentalImaginaryQuadraticDiscriminant (-3 : Int) := by
-- proof
  apply ImaginaryQuadraticDiscriminant.fund_neg_three


-- created on 2026-10-23
-- updated on 2026-10-28
