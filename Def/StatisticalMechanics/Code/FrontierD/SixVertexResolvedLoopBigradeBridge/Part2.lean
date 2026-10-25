/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexResolvedLoopBigradeBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairResolvedInjection.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexLoopPairBigrade.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexResolvedLoopBigradeBridge


namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexExplicitResolvedBigradeFiberEquivLoopMarked
    (T : EvenTorus) (left right : Fin (T.width + 1)) (k : Nat)
    (grade : Nat × Nat) :
    {resolved : SixVertexExplicitResolvedMarkedPair T left right k //
        sixVertexExplicitResolvedBigrade resolved = grade} ≃
      {decorated : SixVertexResolvedLoopMarkedPair T left right k //
        sixVertexResolvedLoopMarkedPairBigrade decorated = grade} :=
  Equiv.subtypeEquiv
    (sixVertexExplicitResolvedMarkedPairEquivLoopMarked T left right k)
    fun resolved => by
      rw [sixVertexExplicitResolvedMarkedPairEquivLoopMarked_bigrade]

noncomputable def sixVertexResolvedLoopMarkedBigradeFiberEquiv
    (T : EvenTorus) (left right : Fin (T.width + 1)) (k : Nat)
    (grade : Nat × Nat) :
    {decorated : SixVertexResolvedLoopMarkedPair T left right k //
        sixVertexResolvedLoopMarkedPairBigrade decorated = grade} ≃
      ({loops : SixVertexLoopDecoratedPair T left right //
          sixVertexLoopDecoratedPairBigrade loops = grade} ×
        Fin (grade.1.choose k)) where
  toFun decorated :=
    (⟨decorated.1.1, decorated.2⟩,
      Fin.cast
        (congrArg (fun g : Nat × Nat => g.1.choose k) decorated.2)
        decorated.1.2)
  invFun decorated :=
    ⟨⟨decorated.1.1,
        Fin.cast
          (congrArg (fun g : Nat × Nat => g.1.choose k)
            decorated.1.2).symm
          decorated.2⟩,
      decorated.1.2⟩
  left_inv decorated := by
    apply Subtype.ext
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Fin.ext
      rfl
  right_inv decorated := by
    apply Prod.ext
    · rfl
    · apply Fin.ext
      rfl

end
end StatMech.FrontierD
