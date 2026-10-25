/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ComponentThirdSplit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteCombinatorics
import Theorem.StatisticalMechanics.Code.Exact3D.BoxPathWitness.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc7componenteven
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part3
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem boundaryVertexDecrementedSourceProfileMajorization_of_weightNonzero
    (h :
      BoundaryVertexDecrementedSourceProfileMajorizationWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  have hvbdry : FK.boxBoundary 3 n v :=
    (Finset.mem_filter.mp hv).2
  calc
    finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum β H n Ω v =
        finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum β H n
          (finiteBoundaryGhostWeightNonzeroCutoff β H n Ω) v :=
      finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_eq_weightNonzeroCutoff
        β H n Ω hvbdry
    _ ≤
        finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile
          β H n (finiteBoundaryGhostWeightNonzeroCutoff β H n Ω) v :=
      hn H hH Ω v hv

set_option linter.style.longLine false in


theorem
    finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_le_boundaryFiberSourcePairVertexProfile_weightNonzeroCutoff_of_filter_le_filter_not_le
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (P :
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) → Prop)
    [DecidablePred P]
    {A B : ℝ}
    (hP :
      finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum β H n
        (Ω.filter P) v ≤ A)
    (hnot :
      finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum β H n
        (Ω.filter fun m => ¬ P m) v ≤ B)
    (hAB :
      A + B ≤
        finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile
          β H n (finiteBoundaryGhostWeightNonzeroCutoff β H n Ω) v) :
    finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum β H n Ω v ≤
      finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile
        β H n (finiteBoundaryGhostWeightNonzeroCutoff β H n Ω) v :=
  finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_le_of_filter_le_filter_not_le
    β H n Ω v P hP hnot hAB

set_option linter.style.longLine false in


theorem
    finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_le_boundaryFiberSourcePairVertexProfile_weightNonzeroCutoff_of_label_sum_le
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (label :
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) → ι)
    {A : ι → ℝ}
    (hcase :
      ∀ i,
        finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum
          β H n (Ω.filter fun m => label m = i) v ≤ A i)
    (hA :
      (∑ i, A i) ≤
        finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile
          β H n (finiteBoundaryGhostWeightNonzeroCutoff β H n Ω) v) :
    finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum β H n Ω v ≤
      finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile
        β H n (finiteBoundaryGhostWeightNonzeroCutoff β H n Ω) v :=
  finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_le_of_label_sum_le
    β H n Ω v label hcase hA

set_option linter.style.longLine false in


theorem
    finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_le_boundaryFiberSourcePairVertexProfile_of_currentSupport_label_sum_le
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (label : Sigma (fun m :
      ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ =>
      finiteBoundaryGhostDecrementedSourceWeightVertexFiber n m v) → ι)
    {A : ι → ℝ}
    (hcase :
      ∀ i,
        (∑ a ∈
            (finiteBoundaryGhostDecrementedSourceWeightVertexSigmaCurrentSupport
              n Ω v).filter (fun a => label a = i),
            finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand
              β H n v a) ≤ A i)
    (hA :
      (∑ i, A i) ≤
        finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile β H n Ω v) :
    finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum β H n Ω v ≤
      finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile β H n Ω v := by
  calc
    finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum β H n Ω v =
        ∑ a ∈
          finiteBoundaryGhostDecrementedSourceWeightVertexSigmaCurrentSupport
            n Ω v,
          finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand
            β H n v a :=
      (finiteBoundaryGhostDecrementedSourceWeightVertexSigmaCurrentSupport_sum_eq_vertexCutoffSum
        β H n Ω v).symm
    _ ≤
        finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile β H n Ω v :=
      finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSubcase_sum_le_of_label_sum_le
        β H
        (finiteBoundaryGhostDecrementedSourceWeightVertexSigmaCurrentSupport
          n Ω v)
        label hcase hA

end Exact3D
end StatMech
