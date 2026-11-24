module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheAnisotropyRoots.Part4
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSpectralIsolation
public import Mathlib.LinearAlgebra.Vandermonde
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheVandermonde
open Finset Filter Matrix Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheVandermonde.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def sixVertexNormalizedBethePairFactor (c : Real) (u v : Complex) : Complex :=
  sixVertexBethePairFactor c u v / (c ^ 2 - 2 : Real)

end
end StatMech.FrontierD
