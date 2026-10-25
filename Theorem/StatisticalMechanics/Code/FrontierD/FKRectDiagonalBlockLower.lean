/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDiagonalBlockLower.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKFiniteConnectionApproximation
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectLocalBoxEmbedding.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectWindingBlockSource.Part3
import Theorem.StatisticalMechanics.Code.FK.TwoPointPathLower
import Theorem.StatisticalMechanics.Code.FrontierD.FiniteProductExceptions
import Def.StatisticalMechanics.Code.FrontierD.FKRectDiagonalBlockLower


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.Percolation Filter Topology

noncomputable section

theorem exists_fkRectRightBand_verticalWalk_length
    (R : FKRectTorus) (cut : Nat) (x : Fin R.width) (hx : cut <= x.val)
    (r n : Nat) (hr : 1 <= r) (hupper : r + n <= R.height - 1) :
    ∃ w : (fkRectInducedGraph R
        (fkRectRightStripBand R cut 1 (R.height - 1))).Walk
          (fkRectRightBandVertexAtRow R cut x hx r ⟨hr, by omega⟩)
          (fkRectRightBandVertexAtRow R cut x hx (r + n)
            ⟨by omega, hupper⟩),
      w.length = n := by
  induction n with
  | zero =>
      exact ⟨.nil, rfl⟩
  | succ n ih =>
      have hnupper : r + n <= R.height - 1 := by omega
      obtain ⟨w, hw⟩ := ih hnupper
      have hlast : 1 <= r + n := by omega
      have hnext : r + n + 1 <= R.height - 1 := by omega
      have hpred : SixVertexArrows.cyclicPred R.height_pos
          (⟨r + n + 1, by omega⟩ : Fin R.height) =
          (⟨r + n, by omega⟩ : Fin R.height) := by
        apply Fin.ext
        rw [fkRectCyclicPred_val]
        simp only [if_neg (by omega : r + n + 1 ≠ 0)]
        omega
      have hadj : (fkRectInducedGraph R
          (fkRectRightStripBand R cut 1 (R.height - 1))).Adj
          (fkRectRightBandVertexAtRow R cut x hx (r + n)
            ⟨hlast, hnupper⟩)
          (fkRectRightBandVertexAtRow R cut x hx (r + n + 1)
            ⟨by omega, hnext⟩) := by
        change (fkRectTorusGraph R).Adj
          (x, (⟨r + n, by omega⟩ : Fin R.height))
          (x, (⟨r + n + 1, by omega⟩ : Fin R.height))
        simpa [hpred] using
          (fkRectTorusGraph_adj_verticalPred R x
            (⟨r + n + 1, by omega⟩ : Fin R.height)).symm
      let w' := w.concat hadj
      refine ⟨?_, ?_⟩
      · simpa [Nat.add_assoc] using w'
      · simp [w', hw]


theorem fkRectWindingBlock_twoPoint_ge_cFE_pow
    {q : Real} (hq : 1 <= q)
    (k scale blocks cut : Nat)
    (x : Fin (fkRectWindingBlockVerticalFamily k scale blocks).width)
    (hx : cut <= x.val) (i : Fin (blocks + 1)) :
    FK.cFE (fkRectCriticalP q) q ^ (2 * (scale + 1)) <=
      FK.twoPointFun
        (fkRectInducedGraph
          (fkRectWindingBlockVerticalFamily k scale blocks)
          (fkRectRightStripBand
            (fkRectWindingBlockVerticalFamily k scale blocks) cut 1
            ((fkRectWindingBlockVerticalFamily k scale blocks).height - 1)))
        (fkRectCriticalP q) q
        (fkRectWindingBlockPathVertex k scale blocks cut x hx i.castSucc)
        (fkRectWindingBlockPathVertex k scale blocks cut x hx i.succ) := by
  let r := 1 + 2 * (scale + 1) * i.val
  have hr : 1 <= r := by omega
  have hupper : r + 2 * (scale + 1) <=
      (fkRectWindingBlockVerticalFamily k scale blocks).height - 1 := by
    have hi : i.val + 1 <= blocks + 1 := by omega
    have hmul := Nat.mul_le_mul_left (2 * (scale + 1)) hi
    calc
      r + 2 * (scale + 1) =
          1 + 2 * (scale + 1) * (i.val + 1) := by
        dsimp [r]
        ring
      _ <= 1 + 2 * (scale + 1) * (blocks + 1) :=
        Nat.add_le_add_left hmul 1
      _ = (fkRectWindingBlockVerticalFamily k scale blocks).height - 1 := by
        simp only [fkRectWindingBlockVerticalFamily_height]
        omega
  obtain ⟨w, hw⟩ := exists_fkRectRightBand_verticalWalk_length
    (fkRectWindingBlockVerticalFamily k scale blocks) cut x hx
    r (2 * (scale + 1)) hr hupper
  have hstart : fkRectRightBandVertexAtRow
      (fkRectWindingBlockVerticalFamily k scale blocks) cut x hx r
        ⟨hr, by omega⟩ =
      fkRectWindingBlockPathVertex k scale blocks cut x hx i.castSucc := by
    apply Subtype.ext
    rfl
  have hend : fkRectRightBandVertexAtRow
      (fkRectWindingBlockVerticalFamily k scale blocks) cut x hx
        (r + 2 * (scale + 1)) ⟨by omega, hupper⟩ =
      fkRectWindingBlockPathVertex k scale blocks cut x hx i.succ := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Fin.ext
      change r + 2 * (scale + 1) =
        1 + 2 * (scale + 1) * (i.val + 1)
      dsimp [r]
      ring
  have hpath := FK.cFE_pow_walk_length_le_twoPoint
    (fkRectInducedGraph
      (fkRectWindingBlockVerticalFamily k scale blocks)
      (fkRectRightStripBand
        (fkRectWindingBlockVerticalFamily k scale blocks) cut 1
        ((fkRectWindingBlockVerticalFamily k scale blocks).height - 1)))
    (fkRectCriticalP_pos (zero_lt_one.trans_le hq))
    (fkRectCriticalP_lt_one (zero_lt_one.trans_le hq)) hq w
  rw [hw] at hpath
  rw [hstart, hend] at hpath
  exact hpath

end
end StatMech.FrontierD
