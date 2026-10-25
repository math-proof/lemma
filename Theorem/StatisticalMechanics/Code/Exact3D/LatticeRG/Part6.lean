/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.StatisticalMechanics.Code.Exact3D.RG.Part2
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Instance.StatisticalMechanics.Code.Exact3D.LatticeRG.Part2


namespace StatMech

namespace Exact3D

open StatMech.Lattice


namespace PolymerSupport

@[simp] theorem union_carrier {d : ℕ} (P Q : PolymerSupport d) :
    (P ∪ Q).carrier = P.carrier ∪ Q.carrier :=
  rfl

@[simp] theorem mem_union {d : ℕ} (P Q : PolymerSupport d) (x : Site d) :
    x ∈ P ∪ Q ↔ x ∈ P ∨ x ∈ Q := by
  change x ∈ P.carrier ∪ Q.carrier ↔ x ∈ P.carrier ∨ x ∈ Q.carrier
  exact Finset.mem_union

@[simp] theorem empty_union {d : ℕ} (P : PolymerSupport d) :
    empty d ∪ P = P := by
  ext x
  simp [empty]

@[simp] theorem union_empty {d : ℕ} (P : PolymerSupport d) :
    P ∪ empty d = P := by
  ext x
  simp [empty]


end PolymerSupport
end Exact3D
end StatMech
