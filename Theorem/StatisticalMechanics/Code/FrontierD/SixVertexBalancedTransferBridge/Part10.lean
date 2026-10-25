/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedTransferBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBalancedBoundaryGluing
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFiniteTorus.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexParticleHole.Part5
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBalancedTransferBridge.Part10
open Finset Matrix


namespace StatMech.FrontierD

theorem svTorusSeam_balanced_iff_lastRow
    (T : EvenTorus) (omega : SixVertexArrows T) :
    (sixVertexTorusSeam T omega).Balanced ↔
      sixVertexUpCount
        (svTorusVerticalRows T omega (svFinLast T.height_pos)) = T.width / 2 := by
  rfl

theorem svTorusBalancedArrowPartitionSum_eq_rowSum
    (T : EvenTorus) (c : Real) :
    svTorusBalancedArrowPartitionSum T c =
      ∑ vrows : Fin T.height → SixVertexRow T.width,
        if sixVertexUpCount (vrows (svFinLast T.height_pos)) = T.width / 2 then
          ∏ j : Fin T.height,
            sixVertexTransfer T.width c
              (vrows (SixVertexArrows.cyclicPred T.height_pos j)) (vrows j)
        else 0 := by
  classical
  rw [svTorusBalancedArrowPartitionSum]
  calc
    (∑ omega : SixVertexArrows T,
      if (sixVertexTorusSeam T omega).Balanced then omega.weight c else 0) =
        ∑ rows : (Fin T.height → SixVertexRow T.width) ×
            (Fin T.height → SixVertexRow T.width),
          if sixVertexUpCount (rows.2 (svFinLast T.height_pos)) = T.width / 2 then
            ∏ j : Fin T.height,
              svHorizontalRowWeight T.width_pos c
                (rows.2 (SixVertexArrows.cyclicPred T.height_pos j))
                (rows.2 j) (rows.1 j)
          else 0 := by
      apply Fintype.sum_equiv (svTorusRowsEquiv T)
      intro omega
      apply if_congr
      · exact svTorusSeam_balanced_iff_lastRow T omega
      · exact svTorusWeight_eq_product_rowWeights T c omega
      · rfl
    _ = ∑ vrows : Fin T.height → SixVertexRow T.width,
          ∑ hrows : Fin T.height → SixVertexRow T.width,
            if sixVertexUpCount (vrows (svFinLast T.height_pos)) = T.width / 2 then
              ∏ j : Fin T.height,
                svHorizontalRowWeight T.width_pos c
                  (vrows (SixVertexArrows.cyclicPred T.height_pos j))
                  (vrows j) (hrows j)
            else 0 := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
    _ = ∑ vrows : Fin T.height → SixVertexRow T.width,
        if sixVertexUpCount (vrows (svFinLast T.height_pos)) = T.width / 2 then
          ∏ j : Fin T.height,
            sixVertexTransfer T.width c
              (vrows (SixVertexArrows.cyclicPred T.height_pos j)) (vrows j)
        else 0 := by
      apply Finset.sum_congr rfl
      intro vrows hvrows
      by_cases hbal :
          sixVertexUpCount (vrows (svFinLast T.height_pos)) = T.width / 2
      · simp only [if_pos hbal]
        rw [← Fintype.prod_sum]
        apply Finset.prod_congr rfl
        intro j hj
        exact svHorizontalRowWeight_sum_eq_transfer T.width_pos c _ _
      · simp [hbal]

theorem svCyclicPred_finitePeriodicSucc {N : Nat} (hN : 0 < N)
    (i : Fin N) :
    SixVertexArrows.cyclicPred hN (finitePeriodicSucc hN i) = i := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  refine Fin.lastCases ?_ (fun i => ?_) i
  · rw [finitePeriodicSucc_last]
    ext
    simp [SixVertexArrows.cyclicPred]
  · rw [finitePeriodicSucc_castSucc, svCyclicPred_succ]

theorem svPredTransferProduct_eq_matrixCycleWeight
    {N M : Nat} (hM : 0 < M) (c : Real)
    (vrows : Fin M → SixVertexRow N) :
    (∏ j : Fin M, sixVertexTransfer N c
        (vrows (SixVertexArrows.cyclicPred hM j)) (vrows j)) =
      matrixCycleWeight hM (sixVertexTransfer N c) vrows := by
  unfold matrixCycleWeight
  let e := svFinitePeriodicSuccEquiv hM
  have he := e.prod_comp (fun j : Fin M =>
    sixVertexTransfer N c
      (vrows (SixVertexArrows.cyclicPred hM j)) (vrows j))
  rw [show (fun i : Fin M =>
      sixVertexTransfer N c
        (vrows (SixVertexArrows.cyclicPred hM (e i))) (vrows (e i))) =
      (fun i : Fin M => sixVertexTransfer N c
        (vrows i) (vrows (finitePeriodicSucc hM i))) by
    funext i
    rw [svFinitePeriodicSuccEquiv_apply,
      svCyclicPred_finitePeriodicSucc]] at he
  exact he.symm

theorem svPeriodicRowsFixedSectorEquiv_weight
    (N M : Nat) (hM : 0 < M) (c : Real) (n : Fin (N + 1))
    (x : SixVertexPeriodicRowsInSector N M hM c n) :
    sixVertexPeriodicRowWeight hM c x.1 =
      matrixCycleWeight hM (sixVertexSectorTransfer N n c)
        (sixVertexPeriodicRowsFixedSectorEquiv N M hM c n x) := by
  rw [sixVertexPeriodicRowWeight, matrixCycleWeight, matrixCycleWeight]
  apply Finset.prod_congr rfl
  intro i hi
  change sixVertexTransfer N c (x.1.1 i)
    (x.1.1 (finitePeriodicSucc hM i)) = _
  simp [sixVertexPeriodicRowsFixedSectorEquiv, sixVertexSectorTransfer]

theorem svPeriodicRowsInSector_sum_eq_trace
    (N M : Nat) (hM : 0 < M) (c : Real) (n : Fin (N + 1)) :
    (∑ x : SixVertexPeriodicRowsInSector N M hM c n,
      sixVertexPeriodicRowWeight hM c x.1) =
      Matrix.trace (sixVertexSectorTransfer N n c ^ M) := by
  calc
    (∑ x : SixVertexPeriodicRowsInSector N M hM c n,
      sixVertexPeriodicRowWeight hM c x.1) =
        ∑ y : MatrixCompatibleCycle hM (sixVertexSectorTransfer N n c),
          matrixCycleWeight hM (sixVertexSectorTransfer N n c) y := by
      apply Fintype.sum_equiv
        (sixVertexPeriodicRowsFixedSectorEquiv N M hM c n)
      exact svPeriodicRowsFixedSectorEquiv_weight N M hM c n
    _ = matrixCompatibleCycleSum hM (sixVertexSectorTransfer N n c) := rfl
    _ = Matrix.trace (sixVertexSectorTransfer N n c ^ M) :=
      matrixCompatibleCycleSum_eq_trace_pow hM _

theorem svTorusBalancedArrowPartitionSum_eq_sectorTrace
    (T : EvenTorus) (c : Real) :
    svTorusBalancedArrowPartitionSum T c =
      Matrix.trace
        (sixVertexSectorTransfer T.width (T.width / 2) c ^ T.height) := by
  classical
  rw [svTorusBalancedArrowPartitionSum_eq_rowSum]
  simp_rw [svPredTransferProduct_eq_matrixCycleWeight T.height_pos c]
  let A := sixVertexTransfer T.width c
  let n : Fin (T.width + 1) := ⟨T.width / 2,
    Nat.lt_succ_of_le (Nat.div_le_self T.width 2)⟩
  let f : (Fin T.height → SixVertexRow T.width) → Real := fun vrows =>
    if sixVertexUpCount (vrows (svFinLast T.height_pos)) = n.val then
      matrixCycleWeight T.height_pos A vrows
    else 0
  have hfiltered :
      (∑ vrows : Fin T.height → SixVertexRow T.width, f vrows) =
        ∑ x : SixVertexPeriodicRows T.width T.height T.height_pos c,
          f x.1 := by
    calc
      (∑ vrows : Fin T.height → SixVertexRow T.width, f vrows) =
          ∑ vrows ∈ Finset.univ.filter (fun vrows =>
            ∀ i, A (vrows i) (vrows (finitePeriodicSucc T.height_pos i)) ≠ 0),
            f vrows := by
        symm
        apply Finset.sum_filter_of_ne
        intro vrows _ hf i
        have hprod : matrixCycleWeight T.height_pos A vrows ≠ 0 := by
          intro hzero
          apply hf
          unfold f
          rw [hzero]
          split_ifs <;> simp
        intro hzero
        apply hprod
        unfold matrixCycleWeight
        exact Finset.prod_eq_zero (Finset.mem_univ i) hzero
      _ = ∑ x : SixVertexPeriodicRows T.width T.height T.height_pos c,
          f x.1 := by
        exact Finset.sum_subtype _ (by simp [A]) f
  change (∑ vrows : Fin T.height → SixVertexRow T.width, f vrows) = _
  rw [hfiltered]
  have hbalance (x : SixVertexPeriodicRows T.width T.height T.height_pos c) :
      sixVertexUpCount (x.1 (svFinLast T.height_pos)) = n.val ↔
        sixVertexUpCount (x.1 ⟨0, T.height_pos⟩) = n.val := by
    rw [sixVertexPeriodicRows_upCount_eq T.height_pos c x
      (svFinLast T.height_pos)]
  have hsector :
      (∑ x : SixVertexPeriodicRows T.width T.height T.height_pos c, f x.1) =
        ∑ x : SixVertexPeriodicRowsInSector
          T.width T.height T.height_pos c n,
          sixVertexPeriodicRowWeight T.height_pos c x.1 := by
    unfold f
    simp_rw [hbalance]
    rw [show (∑ x : SixVertexPeriodicRows T.width T.height T.height_pos c,
        if sixVertexUpCount (x.1 ⟨0, T.height_pos⟩) = n.val then
          matrixCycleWeight T.height_pos A x.1 else 0) =
        ∑ x ∈ Finset.univ.filter (fun x :
          SixVertexPeriodicRows T.width T.height T.height_pos c =>
            sixVertexUpCount (x.1 ⟨0, T.height_pos⟩) = n.val),
          matrixCycleWeight T.height_pos A x.1 by
            rw [Finset.sum_filter]]
    rw [Finset.sum_subtype (p := fun x :
      SixVertexPeriodicRows T.width T.height T.height_pos c =>
        sixVertexUpCount (x.1 ⟨0, T.height_pos⟩) = n.val)
      (Finset.univ.filter fun x :
        SixVertexPeriodicRows T.width T.height T.height_pos c =>
          sixVertexUpCount (x.1 ⟨0, T.height_pos⟩) = n.val)
      (by simp)]
    rfl
  rw [hsector]
  exact svPeriodicRowsInSector_sum_eq_trace
    T.width T.height T.height_pos c n

set_option maxHeartbeats 800000 in

theorem sixVertexRectangleBalancedPartitionSum_eq_torusBalancedArrow
    (T : EvenTorus) (c : Real) :
    sixVertexRectangleBalancedPartitionSum T.width T.height c =
      svTorusBalancedArrowPartitionSum T c := by
  classical
  rw [sixVertexRectangleBalancedPartitionSum,
    svTorusBalancedArrowPartitionSum]
  calc
    (∑ xi : SixVertexToroidalBoundary T.width T.height,
      if xi.Balanced then
        sixVertexRectangleBoundaryPartitionSum T.width T.height c
          (sixVertexToroidalRectangleBoundary xi)
      else 0) =
        ∑ xi : SixVertexToroidalBoundary T.width T.height,
          ∑ omega : {omega : SixVertexRectangleArrows T.width T.height //
            sixVertexRectangleBoundary omega =
              sixVertexToroidalRectangleBoundary xi},
            if xi.Balanced then omega.1.weight c else 0 := by
      apply Finset.sum_congr rfl
      intro xi hxi
      by_cases hbal : xi.Balanced
      · simp only [if_pos hbal]
        exact sixVertexRectangleBoundaryPartitionSum_eq_fiberSum
          T.width T.height c (sixVertexToroidalRectangleBoundary xi)
      · simp [hbal]
    _ = ∑ xiomega : SixVertexCutRectangles T,
          if xiomega.1.Balanced then xiomega.2.1.weight c else 0 := by
      rw [Fintype.sum_sigma]
    _ = ∑ omega : SixVertexArrows T,
          if (sixVertexTorusSeam T omega).Balanced then omega.weight c else 0 := by
      symm
      calc
        (∑ omega : SixVertexArrows T,
          if (sixVertexTorusSeam T omega).Balanced then omega.weight c else 0) =
            ∑ omega : SixVertexArrows T,
              (fun xiomega : SixVertexCutRectangles T =>
                if xiomega.1.Balanced then xiomega.2.1.weight c else 0)
                (sixVertexTorusCutEquiv T omega) := by
          apply Finset.sum_congr rfl
          intro omega homega
          change (if (sixVertexTorusSeam T omega).Balanced then
              omega.weight c else 0) =
            if (sixVertexTorusSeam T omega).Balanced then
              (sixVertexCutTorusArrows T omega).weight c else 0
          rw [sixVertexCutTorusArrows_weight]
        _ = ∑ xiomega : SixVertexCutRectangles T,
              if xiomega.1.Balanced then xiomega.2.1.weight c else 0 :=
          (sixVertexTorusCutEquiv T).sum_comp
            (fun xiomega : SixVertexCutRectangles T =>
              if xiomega.1.Balanced then xiomega.2.1.weight c else 0)

theorem sixVertexRectangleBalancedPartitionSum_eq_halfFilledTrace
    (T : EvenTorus) (c : Real) :
    sixVertexRectangleBalancedPartitionSum T.width T.height c =
      Matrix.trace
        (sixVertexSectorTransfer T.width (T.width / 2) c ^ T.height) := by
  rw [sixVertexRectangleBalancedPartitionSum_eq_torusBalancedArrow]
  exact svTorusBalancedArrowPartitionSum_eq_sectorTrace T c

end StatMech.FrontierD
