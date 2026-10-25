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
import Def.Combinatorics.Enumerative.ZagierCyclicPermutationProduct.Part27
/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

noncomputable instance zagOddMarksDepthFintype {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (d : ℕ) :
    Fintype {q : Σ root, ZagOddMarks e π root // q.2.depth = d} :=
  Fintype.ofEquiv
    {s : Finset (Fin n) //
      s ∈ (zagCycleMinima e π).powersetCard (2 * d + 3)}
    (zagOddMarksDepthEquivPowerset e π d).symm

end MetaMathlibExt
