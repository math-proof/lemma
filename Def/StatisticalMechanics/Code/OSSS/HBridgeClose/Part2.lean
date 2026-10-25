/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/HBridgeClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.OSFKAssemblyClose
import Theorem.StatisticalMechanics.Code.FK.TwoPoint.Part4
import Theorem.StatisticalMechanics.Code.FK.FiniteEnergy.Part4
import Theorem.StatisticalMechanics.Code.OSSS.HBridgeClose
open scoped BigOperators Classical
open Finset Real Set Filter Topology


namespace StatMech

namespace OSSS

namespace HBridgeClose

open StatMech.FK

open StatMech.OSSS.OSFKAssemblyClose

open StatMech.OSSS.BetaCMatch

variable {V : Type*} [Fintype V] [DecidableEq V]


noncomputable def flipEquiv (e : Sym2 V) : ConfigSpace (Sym2 V) ≃ ConfigSpace (Sym2 V) where
  toFun := flipE e
  invFun := flipE e
  left_inv := flipE_flipE e
  right_inv := flipE_flipE e

end HBridgeClose
end OSSS
end StatMech
