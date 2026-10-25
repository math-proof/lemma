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
import Theorem.Combinatorics.Enumerative.ZagierCyclicPermutationProduct.Part36
/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

abbrev ZagOriginalPoints {n : ℕ} {hn : 0 < n} {k l : ℕ}
    (q : ZagPlaneConfigBy n hn k l) :=
  {x : Fin n // zagNontrivialAntiExceedance q.1.1.1 q.1.2 x}

abbrev ZagReflectedPoints {n : ℕ} {hn : 0 < n} {k l : ℕ}
    (q : ZagPlaneConfigBy n hn k l) :=
  {x : Fin n // zagNontrivialAntiExceedance
    (zagReverseOrder hn q.1.1.1) (zagDiagonal q.1.1.1 q.1.2)⁻¹ x}

end MetaMathlibExt
