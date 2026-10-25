/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheTailLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheTailSelectedDensity
import Mathlib.Topology.ContinuousMap.Ordered
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheTailLimit.Part3


namespace StatMech.FrontierD

noncomputable section

open Filter Topology

theorem continuous_sixVertexTailRootDensity
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c) :
    Continuous (sixVertexTailRootDensity hc htail) := by
  apply Continuous.div
  · exact (sixVertexTailWeightedDensityLimitMap hc htail |>.IccExtend
      (by linarith [Real.pi_pos])).continuous
  · unfold sixVertexRootDensityWeight sixVertexBetheIntegratingFactor
      sixVertexRootDensityScale
    fun_prop
  · intro x
    exact (sixVertexRootDensityWeight_pos hc x).ne'

theorem sixVertexRootDensityWeight_mul_tailRootDensity_of_mem
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c)
    {x : Real} (hx : x ∈ Set.Icc (-Real.pi) Real.pi) :
    sixVertexRootDensityWeight c x * sixVertexTailRootDensity hc htail x =
      sixVertexTailWeightedDensityLimitMap hc htail ⟨x, hx⟩ := by
  have hlimit : sixVertexTailWeightedDensityLimit hc htail x =
      sixVertexTailWeightedDensityLimitMap hc htail ⟨x, hx⟩ := by
    unfold sixVertexTailWeightedDensityLimit
    rw [ContinuousMap.coe_IccExtend,
      Set.IccExtend_of_mem (by linarith [Real.pi_pos]) _ hx]
  rw [sixVertexTailRootDensity, hlimit]
  field_simp [(sixVertexRootDensityWeight_pos hc x).ne']

theorem tendsto_sixVertexSelectedWeightedDensity_at
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c)
    {x : Real} (hx : x ∈ Set.Icc (-Real.pi) Real.pi) :
    Tendsto (fun k => sixVertexRootDensityWeight c x *
        sixVertexSelectedFiniteRootDensity hc k x) atTop
      (nhds (sixVertexRootDensityWeight c x *
        sixVertexTailRootDensity hc htail x)) := by
  have heval := (continuous_eval_const (⟨x, hx⟩ :
      Set.Icc (-Real.pi) Real.pi)).tendsto
    (sixVertexTailWeightedDensityLimitMap hc htail)
  have h := heval.comp
    (tendsto_sixVertexSelectedWeightedDensityMap hc htail)
  have htarget : sixVertexRootDensityWeight c x *
      sixVertexTailRootDensity hc htail x =
        sixVertexTailWeightedDensityLimitMap hc htail ⟨x, hx⟩ := by
    exact sixVertexRootDensityWeight_mul_tailRootDensity_of_mem hc htail hx
  rw [htarget]
  simpa [Function.comp_def, sixVertexSelectedWeightedDensityMap] using h

end
end StatMech.FrontierD
