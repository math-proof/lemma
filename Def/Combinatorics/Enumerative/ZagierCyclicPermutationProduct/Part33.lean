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
import Abbrev.Combinatorics.Enumerative.ZagierCyclicPermutationProduct
/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

noncomputable def zagPlaneConfigEquivPairs (n k : ℕ) (hn : 0 < n) :
    ZagPlaneConfig n hn k ≃ ZagPlanePairs n k := by
  let E := zagAnchoredOrderEquivFullCycle n hn
  refine {
    toFun := fun p =>
      ⟨(E p.1.1, p.1.2), by
        have he : (E p.1.1).1 = zagHorizontal p.1.1.1 := rfl
        exact ⟨p.2.1, by simpa only [zagDiagonal, he] using p.2.2⟩⟩
    invFun := fun p =>
      ⟨(E.symm p.1.1, p.1.2), by
        have he : zagHorizontal (E.symm p.1.1).1 = p.1.1.1 := by
          exact congrArg Subtype.val (E.apply_symm_apply p.1.1)
        exact ⟨p.2.1, by simpa only [zagDiagonal, he] using p.2.2⟩⟩
    left_inv := ?_
    right_inv := ?_
  }
  · intro p
    apply Subtype.ext
    apply Prod.ext
    · exact E.symm_apply_apply p.1.1
    · rfl
  · intro p
    apply Subtype.ext
    apply Prod.ext
    · exact E.apply_symm_apply p.1.1
    · rfl

noncomputable def zagReverseIndex (n : ℕ) (hn : 0 < n) :
    Equiv.Perm (Fin n) := by
  let hNeZero : NeZero n := ⟨hn.ne'⟩
  exact Equiv.neg (Fin n)

end MetaMathlibExt
