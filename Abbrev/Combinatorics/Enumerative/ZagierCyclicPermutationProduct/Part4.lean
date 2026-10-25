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
import Theorem.Combinatorics.Enumerative.ZagierCyclicPermutationProduct.Part38
/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

abbrev ZagPointedConfigBy (n : ℕ) (hn : 0 < n) (k l : ℕ) :=
  {p : ZagPointedPlane n //
    p.order (zagBasePoint ⟨0, hn⟩) = zagBasePoint ⟨0, hn⟩ ∧
      cycleQuotientCount p.vertical = k ∧
      cycleQuotientCount (zagDiagonal p.order p.vertical) = l}

end MetaMathlibExt
