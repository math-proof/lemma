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
import Abbrev.Combinatorics.Enumerative.ZagierCyclicPermutationProduct.Part6
/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

noncomputable def zagOddMarkedDepthFiberEquiv
    (n : ℕ) (hn : 0 < n) (k l : ℕ) (d : Fin n) :
    {q : ZagOddMarkedConfigBy n hn k l //
        (⟨q.1.marks.depth, q.1.marks.depth_lt⟩ : Fin n) = d} ≃
      Σ c : ZagPlaneConfigBy n hn (k + 2 * (d.val + 1)) l,
        {m : Σ root, ZagOddMarks c.1.1.1 c.1.2 root //
          m.2.depth = d.val} where
  toFun q := by
    have hdepth : q.1.1.marks.depth = d.val := congrArg Fin.val q.2
    let c : ZagPlaneConfigBy n hn (k + 2 * (d.val + 1)) l :=
      ⟨(⟨q.1.1.order, q.1.2.1⟩, q.1.1.vertical), by
        exact ⟨by simpa only [hdepth] using q.1.2.2.1, q.1.2.2.2⟩⟩
    exact ⟨c, ⟨⟨q.1.1.root, q.1.1.marks⟩, hdepth⟩⟩
  invFun r := by
    let c := r.1
    let m := r.2.1
    let q : ZagOddMarkedConfigBy n hn k l := by
      refine ⟨⟨c.1.1.1, c.1.2, m.1, m.2⟩, c.1.1.2, ?_, c.2.2⟩
      rw [c.2.1, r.2.2]
    refine ⟨q, ?_⟩
    apply Fin.ext
    exact r.2.2
  left_inv q := by
    apply Subtype.ext
    apply Subtype.ext
    apply zagOddMarkedPlane_ext <;> rfl
  right_inv r := by
    rcases r with ⟨c, ⟨⟨root, marks⟩, hdepth⟩⟩
    apply Sigma.ext
    · rfl
    · exact HEq.rfl

noncomputable def zagOddMarkedConfigByEquivDepthDecomposition
    (n : ℕ) (hn : 0 < n) (k l : ℕ) :
    ZagOddMarkedConfigBy n hn k l ≃
      ZagMarkedDepthDecomposition n hn k l := by
  let depthIndex : ZagOddMarkedConfigBy n hn k l → Fin n := fun q =>
    ⟨q.1.marks.depth, q.1.marks.depth_lt⟩
  exact (Equiv.sigmaFiberEquiv depthIndex).symm.trans
    (Equiv.sigmaCongrRight fun d => zagOddMarkedDepthFiberEquiv n hn k l d)

end MetaMathlibExt
