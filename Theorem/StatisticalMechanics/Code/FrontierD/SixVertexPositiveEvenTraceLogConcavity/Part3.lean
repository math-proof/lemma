/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveEvenTraceLogConcavity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexTwoCycleCapacityHall.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexSectorPerronLogConcavity.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexPositiveEvenTraceLogConcavity.Part3
open Filter Matrix Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexSectorPositiveEvenTraceLogConcave_of_keyCapacityHall
    (N : Nat) (hNpos : 0 < N) (hNeven : Even N)
    {c : Real} (hc : 2 <= c)
    (hHall : SixVertexPositiveEvenTraceKeyCapacityHall N hNpos hNeven) :
    SixVertexSectorPositiveEvenTraceLogConcave N c := by
  intro M n hn0 hnN
  let T := sixVertexPositiveEvenTorus N M hNpos hNeven
  let middle : Fin (T.width + 1) := ⟨n, by
    change n < N + 1
    omega⟩
  have hcapacity : SixVertexHorizontalTwoCycleKeyCapacityHall T middle
      hn0 hnN := by
    simpa [T, middle, sixVertexPositiveEvenTorus] using
      hHall M n hn0 hnN
  simpa [T, middle, sixVertexPositiveEvenTorus] using
    (sixVertexSectorTrace_logConcave_of_keyCapacityHall
      T middle hn0 hnN hc hcapacity)


theorem sixVertexSectorPerronLogConcave_of_positiveEvenTraceKeyCapacityHall
    (N : Nat) (hNpos : 0 < N) (hNeven : Even N)
    {c : Real} (hc : 2 <= c)
    (hHall : SixVertexPositiveEvenTraceKeyCapacityHall N hNpos hNeven) :
    SixVertexSectorPerronLogConcave N c :=
  sixVertexSectorPerronLogConcave_of_positiveEvenTraceLogConcave N
    (by linarith)
    (sixVertexSectorPositiveEvenTraceLogConcave_of_keyCapacityHall
      N hNpos hNeven hc hHall)

end
end StatMech.FrontierD
