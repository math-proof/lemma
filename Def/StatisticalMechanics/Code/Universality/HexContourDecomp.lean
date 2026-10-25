/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexContourDecomp.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexBoundary.Part4
import Structure.StatisticalMechanics.Code.Universality.HexContourDecomp


namespace StatMech.Universality

open Complex

open scoped BigOperators


namespace HexSide

variable {V : Type*} [DecidableEq V] {D : HexDomain V}


noncomputable def fSum (s : HexSide D) : ℂ :=
  ∑ e ∈ s.cells, D.obs (D.mid e.vtx e.edge)


noncomputable def incSum (s : HexSide D) : ℂ :=
  ∑ e ∈ s.cells, D.incTerm e


end HexSide
end StatMech.Universality
