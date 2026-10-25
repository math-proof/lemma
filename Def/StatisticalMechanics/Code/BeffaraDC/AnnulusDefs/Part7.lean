/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnnulusDefs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.TwoDim.Crossings.Part4
import Theorem.StatisticalMechanics.Code.BeffaraDC.AnnulusDefs.Part6
open Set
open StatMech.Lattice
open SimpleGraph


namespace StatMech

namespace BeffaraDC

def diagReflIso : hypercubicLattice 2 ≃g hypercubicLattice 2 :=
  ⟨diagReflEquiv, fun {x y} => diagRefl_adj x y⟩

end BeffaraDC
end StatMech
