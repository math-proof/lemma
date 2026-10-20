import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.SmarandachePermutationSequence
open MetaMathlibExt


/--
[smarandacheBlock_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/SmarandachePermutationSequence.lean)
-/
@[path]
private lemma smarandacheBlock_one_eq
  :
-- imply
  smarandacheBlock 1 = [1, 2] := by
-- proof
  apply MetaMathlibExt.smarandacheBlock_one

/--
[smarandacheBlock_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/SmarandachePermutationSequence.lean)
-/
@[path]
private lemma smarandacheBlock_two_eq
  :
-- imply
  smarandacheBlock 2 = [1, 3, 4, 2] := by
-- proof
  apply MetaMathlibExt.smarandacheBlock_two

/--
[smarandacheBlock_three](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/SmarandachePermutationSequence.lean)
-/
@[path]
private lemma smarandacheBlock_three_eq
  :
-- imply
  smarandacheBlock 3 = [1, 3, 5, 6, 4, 2] := by
-- proof
  apply MetaMathlibExt.smarandacheBlock_three

/--
[smarandacheBlock_four](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/SmarandachePermutationSequence.lean)
-/
@[path]
private lemma smarandacheBlock_four_eq
  :
-- imply
  smarandacheBlock 4 = [1, 3, 5, 7, 8, 6, 4, 2] := by
-- proof
  apply MetaMathlibExt.smarandacheBlock_four

/--
[smarandachePrefix_three](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/SmarandachePermutationSequence.lean)
-/
@[path]
private lemma smarandachePrefix_three_eq
  :
-- imply
  smarandachePrefix 3 = [1, 2, 1, 3, 4, 2, 1, 3, 5, 6, 4, 2] := by
-- proof
  apply MetaMathlibExt.smarandachePrefix_three

/--
[smarandachePermutation_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/SmarandachePermutationSequence.lean)
-/
@[path]
private lemma smarandachePermutation_zero_eq
  :
-- imply
  smarandachePermutation 0 = 1 := by
-- proof
  apply MetaMathlibExt.smarandachePermutation_zero

/--
[smarandachePermutation_five](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/SmarandachePermutationSequence.lean)
-/
@[path]
private lemma smarandachePermutation_five_eq
  :
-- imply
  smarandachePermutation 5 = 2 := by
-- proof
  apply MetaMathlibExt.smarandachePermutation_five

/--
[smarandachePermutation_eleven](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/SmarandachePermutationSequence.lean)
-/
@[path]
private lemma smarandachePermutation_eleven_eq
  :
-- imply
  smarandachePermutation 11 = 2 := by
-- proof
  apply MetaMathlibExt.smarandachePermutation_eleven


-- created on 2026-10-20
