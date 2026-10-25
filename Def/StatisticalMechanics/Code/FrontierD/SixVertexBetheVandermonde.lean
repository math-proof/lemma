/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheVandermonde.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheAnisotropyRoots.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSpectralIsolation
import Mathlib.LinearAlgebra.Vandermonde
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheVandermonde
open Finset Filter Matrix Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexNormalizedBethePairFactor (c : Real) (u v : Complex) : Complex :=
  sixVertexBethePairFactor c u v / (c ^ 2 - 2 : Real)

end
end StatMech.FrontierD
