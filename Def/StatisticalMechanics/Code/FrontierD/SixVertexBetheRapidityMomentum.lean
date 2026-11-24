module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierKernelClosedForm
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheRapidityMomentum


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRapidityMomentum.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def sixVertexXiFourierTermContinuous
    (lam : Real) (n : Nat) : C(Real, Real) :=
  ⟨sixVertexXiFourierTerm lam n, by
    unfold sixVertexXiFourierTerm
    fun_prop⟩

end
end StatMech.FrontierD
