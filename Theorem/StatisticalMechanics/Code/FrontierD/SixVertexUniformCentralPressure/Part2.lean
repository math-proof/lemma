/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexUniformCentralPressure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBalancedShareSpectralGapLogConcavity.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedTraceParticleHole
import Def.StatisticalMechanics.Code.FrontierD.SixVertexUniformCentralPressure
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexAllHeightCentralTraceMaximal_of_traceLogConcave
    (N : Nat) (hN : Even N) {c : Real} (hc : 0 < c)
    (hlc : SixVertexSectorTraceLogConcave N c) :
    SixVertexAllHeightCentralTraceMaximal N c := by
  intro M n hM hn
  let a : Nat -> Real := fun sector =>
    Matrix.trace (sixVertexSectorTransfer N sector c ^ M)
  have hpos : forall sector, sector <= N -> 0 < a sector := by
    intro sector hsector
    exact sixVertexSector_trace_pow_pos hsector hc M
  have hsym : forall sector, sector <= N ->
      a (N - sector) = a sector := by
    intro sector hsector
    exact sixVertexSectorTrace_particleHole_uniformPressure hsector M c
  have hlocal : forall sector, 0 < sector -> sector < N ->
      a (sector - 1) * a (sector + 1) <= a sector ^ 2 := by
    intro sector hsector0 hsectorN
    have h := hlc M sector hM hsector0 hsectorN
    rw [sixVertexSectorTraceProfile_eq (by omega),
      sixVertexSectorTraceProfile_eq (by omega),
      sixVertexSectorTraceProfile_eq (by omega)] at h
    exact h
  change a n <= a (N / 2)
  by_cases hnHalf : n <= N / 2
  · exact lowerHalf_le_middle_of_pos_logConcave_symmetric
      a N hN hpos hsym hlocal hnHalf
  · rw [← hsym n hn]
    apply lowerHalf_le_middle_of_pos_logConcave_symmetric
      a N hN hpos hsym hlocal
    obtain ⟨half, rfl⟩ := hN
    omega

theorem sixVertexUniformHeightCentralTraceBound_of_allHeightCentralTraceMaximal
    (N : Nat) {c : Real}
    (hmax : SixVertexAllHeightCentralTraceMaximal N c) :
    SixVertexUniformHeightCentralTraceBound N c := by
  refine ⟨(N + 1 : Nat), by positivity, ?_⟩
  intro M hM
  rw [sixVertexFixedWidthPartitionSum_eq_sum_sector_traces N M hM]
  calc
    _ <= ∑ _sector : Fin (N + 1),
        Matrix.trace (sixVertexSectorTransfer N (N / 2) c ^ M) := by
      apply Finset.sum_le_sum
      intro sector _
      exact hmax M sector.val hM (by omega)
    _ = _ := by simp

theorem sixVertexUniformHeightCentralTraceBound_of_traceLogConcave
    (N : Nat) (hN : Even N) {c : Real} (hc : 0 < c)
    (hlc : SixVertexSectorTraceLogConcave N c) :
    SixVertexUniformHeightCentralTraceBound N c :=
  sixVertexUniformHeightCentralTraceBound_of_allHeightCentralTraceMaximal N
    (sixVertexAllHeightCentralTraceMaximal_of_traceLogConcave
      N hN hc hlc)


end
end StatMech.FrontierD
