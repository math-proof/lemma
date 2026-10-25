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
import Abbrev.Combinatorics.Enumerative.ZagierCyclicPermutationProduct.Part4
/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

def zagOriginalTotalEquivPointedConfigBy
    (n : ℕ) (hn : 0 < n) (k l : ℕ) :
    ZagOriginalTotal n hn k l ≃ ZagPointedConfigBy n hn k l where
  toFun q :=
    ⟨⟨q.1.1.1.1, q.1.1.2, q.2.1, q.2.2⟩,
      q.1.1.1.2, q.1.2.1, q.1.2.2⟩
  invFun p :=
    ⟨⟨(⟨p.1.order, p.2.1⟩, p.1.vertical), ⟨p.2.2.1, p.2.2.2⟩⟩,
      ⟨p.1.point, p.1.point_property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

end MetaMathlibExt
