module
public import Mathlib
public import Def.StatisticalMechanics.Code.Exact3D.RG.Part2
public import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Instance.StatisticalMechanics.Code.Exact3D.LatticeRG


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Exact3D

open StatMech.Lattice


namespace PolymerSupport

@[simp] theorem mem_def {d : ℕ} (P : PolymerSupport d) (x : Site d) :
    x ∈ P ↔ x ∈ P.carrier :=
  Iff.rfl

@[ext] theorem ext {d : ℕ} {P Q : PolymerSupport d}
    (h : ∀ x : Site d, x ∈ P ↔ x ∈ Q) : P = Q := by
  cases P with
  | mk Pc =>
    cases Q with
    | mk Qc =>
      congr
      ext x
      exact h x


end PolymerSupport
end Exact3D
end StatMech
