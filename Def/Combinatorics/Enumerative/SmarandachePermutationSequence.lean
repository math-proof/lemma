/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/SmarandachePermutationSequence.lean -/

import Mathlib.Data.List.Basic
/-!
# Smarandache permutation sequence (A004741)

Formalizes the required definition clause for the Smarandache permutation
sequence (concept `jis_sem_23e7b5e48daf56d0a358ebfc`), as given in statement
`jis_c46e1d9809a20ee69374dac7` of source `jis_source_02ccad5fb16b7cd8775ba04c`
(Kimberling, JIS VOL25): the concatenation of the blocks
`(1, 3, ..., 2n - 1, 2n, 2n - 2, ..., 2)`, whose initial terms are
`(1, 2, 1, 3, 4, 2, 1, 3, 5, 6, 4, 2, 1, 3, 5, 7, 8, 6, 4, 2, ...)`.

Source: Clark Kimberling, *Parasequences*:
<https://cs.uwaterloo.ca/journals/JIS/VOL25/Kimberling/kimber16.tex>.
-/


namespace MetaMathlibExt

/-- The `n`-th block of the Smarandache permutation sequence
(concept `jis_sem_23e7b5e48daf56d0a358ebfc`, statement
`jis_c46e1d9809a20ee69374dac7`): the odd numbers `1, 3, ..., 2n - 1`
followed by the even numbers `2n, 2n - 2, ..., 2`. -/
def smarandacheBlock (n : ℕ) : List ℕ :=
  ((List.range n).map (fun k => 2 * k + 1)) ++ ((List.range n).map (fun k => 2 * (n - k)))

/-- Flattened prefix of the first `N` blocks of the Smarandache permutation
sequence (concept `jis_sem_23e7b5e48daf56d0a358ebfc`, statement
`jis_c46e1d9809a20ee69374dac7`). -/
def smarandachePrefix (N : ℕ) : List ℕ :=
  ((List.range N).map (fun n => smarandacheBlock (n + 1))).flatten

/-- The Smarandache permutation sequence A004741
(concept `jis_sem_23e7b5e48daf56d0a358ebfc`, statement
`jis_c46e1d9809a20ee69374dac7`): the concatenation of the blocks
`(1, 3, ..., 2n - 1, 2n, 2n - 2, ..., 2)`, so it begins
`(1, 2, 1, 3, 4, 2, 1, 3, 5, 6, 4, 2, ...)`. -/
def smarandachePermutation (i : ℕ) : ℕ :=
  (smarandachePrefix (i + 1)).getD i 0

end MetaMathlibExt
