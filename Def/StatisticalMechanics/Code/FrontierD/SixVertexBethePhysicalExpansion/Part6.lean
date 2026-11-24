module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalReduction.Part2
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalExpansion.Part5
open Finset Matrix


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePhysicalExpansion.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def sixVertexBetheWordMLSet {n : Nat}
    (w : Finset (Fin (n + 1))) : Finset (Fin (n + 1)) :=
  Finset.univ.filter fun i => i ∉ w ∧ finRotate (n + 1) i ∈ w

end
end StatMech.FrontierD
