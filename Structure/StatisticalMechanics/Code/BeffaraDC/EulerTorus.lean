/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/EulerTorus.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.EulerGeneral
import Def.StatisticalMechanics.Code.BeffaraDC.EulerTorus
open SimpleGraph Set

set_option linter.unusedSectionVars false


namespace StatMech.BeffaraDC

variable {V : Type*} [Finite V] [DecidableEq V]

open StatMech.Lattice (nullity faceCount euler_general euler_general_nat card_le_edgeSet_add_components)


structure IsTorusDefect (G : SimpleGraph V) (δ : ℕ) : Prop where
  
  le_two : δ ≤ 2
  
  le_nullity : δ ≤ nullity G


end StatMech.BeffaraDC
