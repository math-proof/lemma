/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWSelfDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Ising.Gibbs.Part6
import Def.StatisticalMechanics.Code.Ising.KWSelfDuality.Part2
open scoped BigOperators
open Finset


namespace StatMech

namespace Ising

section HighTemp

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


instance (F : Finset (Sym2 V)) : Decidable (IsEvenSubgraph F) :=
  Fintype.decidableForallFintype


end HighTemp
end Ising
end StatMech
