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
open scoped BigOperators Classical
open Finset Real Set Filter Topology


namespace StatMech

namespace OSSS

namespace HBridgeClose

open StatMech.FK

open StatMech.OSSS.OSFKAssemblyClose

open StatMech.OSSS.BetaCMatch

variable {V : Type*} [Fintype V] [DecidableEq V]


noncomputable def flipE (e : Sym2 V) (ω : ConfigSpace (Sym2 V)) : ConfigSpace (Sym2 V) :=
  Function.update ω e (!ω e)

end HBridgeClose
end OSSS
end StatMech
