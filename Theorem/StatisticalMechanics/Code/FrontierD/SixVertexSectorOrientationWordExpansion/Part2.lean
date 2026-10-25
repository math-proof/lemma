/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexSectorOrientationWordExpansion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexSectorOrientedSplit
import Def.StatisticalMechanics.Code.FrontierD.SixVertexSectorOrientationWordExpansion.Part2
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

theorem trace_sixVertexSectorTransfer_pow_eq_sum_wordTrace
    (N n M : Nat) (c : Real) :
    Matrix.trace (sixVertexSectorTransfer N n c ^ M) =
      ∑ word : Fin M -> Bool,
        sixVertexOrientationWordTrace N M c n word :=
  trace_sixVertexSectorTransfer_pow_eq_sum_orientationWords N n M c


theorem traceProduct_sixVertexSectorTransfer_pow_eq_sum_wordPairs
    (N nLeft nRight M : Nat) (c : Real) :
    Matrix.trace (sixVertexSectorTransfer N nLeft c ^ M) *
        Matrix.trace (sixVertexSectorTransfer N nRight c ^ M) =
      ∑ leftWord : Fin M -> Bool,
        ∑ rightWord : Fin M -> Bool,
          sixVertexOrientationWordTrace N M c nLeft leftWord *
            sixVertexOrientationWordTrace N M c nRight rightWord := by
  rw [trace_sixVertexSectorTransfer_pow_eq_sum_wordTrace,
    trace_sixVertexSectorTransfer_pow_eq_sum_wordTrace,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro leftWord hleftWord
  rw [Finset.mul_sum]


theorem sixVertexSectorTrace_logConcave_iff_wordPairSum
    (N M n : Nat) (c : Real) :
    Matrix.trace (sixVertexSectorTransfer N (n - 1) c ^ M) *
          Matrix.trace (sixVertexSectorTransfer N (n + 1) c ^ M) <=
        Matrix.trace (sixVertexSectorTransfer N n c ^ M) ^ 2 <->
      (∑ leftWord : Fin M -> Bool,
          ∑ rightWord : Fin M -> Bool,
            sixVertexOrientationWordTrace N M c (n - 1) leftWord *
              sixVertexOrientationWordTrace N M c (n + 1) rightWord) <=
        ∑ leftWord : Fin M -> Bool,
          ∑ rightWord : Fin M -> Bool,
            sixVertexOrientationWordTrace N M c n leftWord *
              sixVertexOrientationWordTrace N M c n rightWord := by
  rw [<- traceProduct_sixVertexSectorTransfer_pow_eq_sum_wordPairs,
    <- traceProduct_sixVertexSectorTransfer_pow_eq_sum_wordPairs]
  rw [pow_two]

end
end StatMech.FrontierD
