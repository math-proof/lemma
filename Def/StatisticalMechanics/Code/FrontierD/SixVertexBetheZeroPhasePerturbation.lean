/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhasePerturbation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOddPhysicalExpansion
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexBethePerturbRoot {n : Nat} (p : Fin n → Real)
    (ell : Fin n) (eps : Real) : Fin n → Real :=
  fun j => if j = ell then eps else p j

end
end StatMech.FrontierD
