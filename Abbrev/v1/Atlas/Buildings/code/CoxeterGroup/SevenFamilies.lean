/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/SevenFamilies.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.Coxeter.Basic
import Def.v1.Atlas.Buildings.code.CoxeterGroup.TypeACoxeterSystem.Part2
import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.TypeAInjectivityHelper
import Def.v1.Atlas.Buildings.code.CoxeterGroup.SignedPermGroup.Part2
import Def.v1.Atlas.Buildings.code.CoxeterGroup.TypeCInjectivityHelper


namespace CoxeterMatrix

/-- The Coxeter matrix of type $A_{n-1}$ (linear Dynkin diagram with $n$ nodes). -/
abbrev typeA (n : ℕ) : CoxeterMatrix (Fin n) := CoxeterMatrix.A n

/-- The Coxeter matrix of type $C_n$ (also denoted $B_n$ in Mathlib): hyperoctahedral group. -/
abbrev typeC (n : ℕ) : CoxeterMatrix (Fin n) := CoxeterMatrix.B n

/-- The Coxeter matrix of type $D_n$ (fork at one end). -/
abbrev typeD (n : ℕ) : CoxeterMatrix (Fin n) := CoxeterMatrix.D n

end CoxeterMatrix
