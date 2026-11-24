module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheRegularizedLogTaylor.Part4
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOffsetConvergence
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalCandidateDecomposition
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheRegularizedLogBulk


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRegularizedLogBulk.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

open Finset Filter Topology

noncomputable section

def sixVertexCanonicalEvenRegularizedFullLinearTerm
    {c : Real} (hc : 2 < c) (epsilon : Real) (s k : Nat) : Real :=
  let N := sixVertexFourWidth (2 * s) k
  let q := sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k
  ∑ i, sixVertexRegularizedBetheLogNormDerivative c epsilon (q i) *
      sixVertexCanonicalEvenChargeOffset hc s k i / N

end
end StatMech.FrontierD
