/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wdjdufourdjct.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Walls.welenterleave.Part2
open Finset Set SimpleGraph
open scoped BigOperators


namespace StatMech

namespace Lattice

open StatMech.Walls


structure wdj_Hypermap where
  
  D : Type
  
  [finD : Fintype D]
  
  [decD : DecidableEq D]
  
  α₀ : Equiv.Perm D
  
  α₁ : Equiv.Perm D

end Lattice
end StatMech
