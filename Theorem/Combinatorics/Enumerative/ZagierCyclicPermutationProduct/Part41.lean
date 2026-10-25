/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ZagierCyclicPermutationProduct.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.GroupTheory.Perm.Fin
import Def.Combinatorics.Enumerative.Stirling.Part4
import Lemma.Finset.Enumerative.Stirling
import Def.Combinatorics.Enumerative.ZagierCyclicPermutationProduct.Part41
/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

theorem zagReflectConfig_involutive
    (n : ℕ) (hn : 0 < n) (k l : ℕ)
    (q : ZagPlaneConfigBy n hn k l) :
    zagReflectConfig n hn l k (zagReflectConfig n hn k l q) = q := by
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact zagReverseOrder_reverseOrder hn q.1.1.1
  · exact congrArg Inv.inv (zagDiagonal_reflected hn q.1.1.1 q.1.2)

end MetaMathlibExt
