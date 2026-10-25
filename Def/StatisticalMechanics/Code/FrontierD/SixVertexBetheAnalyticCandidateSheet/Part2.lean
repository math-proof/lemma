/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheAnalyticCandidateSheet.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheAnalyticStabilitySheet
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheVandermonde.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheAnalyticCandidateSheet.Part2
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexHalfFilledBetheContinuationPoint
    {a b c₀ : Real} (ha : 2 < a) (hc₀ : c₀ ∈ Set.Icc a b) (k : Nat) :
    SixVertexBetheContinuationSpace a b (sixVertexFourWidth 0 k)
      ((k + 1) + (k + 1)) := by
  let hc : 2 < c₀ := ha.trans_le hc₀.1
  let p := sixVertexHalfFilledBetheRoots hc k
  have hopen : SixVertexOpenRootSimplex p :=
    sixVertexHalfFilledBetheRoots_mem_open hc k
  have hsol : SixVertexSatisfiesBetheEquations c₀
      (sixVertexFourWidth 0 k) ((k + 1) + (k + 1)) p :=
    sixVertexHalfFilledBetheRoots_is_solution hc k
  have hN : 0 < sixVertexFourWidth 0 k := sixVertexFourWidth_pos 0 k
  exact ⟨(c₀, p), hc₀, hopen.toClosed,
    (sixVertexBetheUpdate_eq_self_iff hN p).mpr hsol⟩

end
end StatMech.FrontierD
