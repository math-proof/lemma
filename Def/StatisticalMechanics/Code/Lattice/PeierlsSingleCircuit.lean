/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsSingleCircuit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.ContourCountInjection.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsSingleCircuit
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

attribute [local instance] Classical.propDecidable


namespace EulerianExistence

variable {V : Type*} [Fintype V] [DecidableEq V]


noncomputable def spliceWalk (G : SimpleGraph V) {u w : V} (p : G.Walk u u)
    (hw : w ∈ p.support) (c : G.Walk w w) : G.Walk u u :=
  (p.takeUntil w hw).append (c.append (p.dropUntil w hw))

end EulerianExistence
end Lattice
end StatMech
