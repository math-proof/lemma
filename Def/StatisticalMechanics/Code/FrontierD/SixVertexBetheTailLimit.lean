module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheTailSelectedDensity
public import Mathlib.Topology.ContinuousMap.Ordered


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheTailLimit.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

open Filter Topology

def sixVertexSelectedWeightedDensityMap
    {c : Real} (hc : 2 < c) (k : Nat) :
    C(Set.Icc (-Real.pi) Real.pi, Real) where
  toFun x := sixVertexRootDensityWeight c x *
    sixVertexSelectedFiniteRootDensity hc k x
  continuous_toFun := by
    apply Continuous.mul
    · unfold sixVertexRootDensityWeight sixVertexBetheIntegratingFactor
        sixVertexRootDensityScale
      fun_prop
    · exact (continuous_sixVertexFiniteRootDensity hc
        (sixVertexFourWidth 0 k) _ _).comp continuous_subtype_val

end
end StatMech.FrontierD
