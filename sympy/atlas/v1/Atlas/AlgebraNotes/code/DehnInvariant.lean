/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/DehnInvariant.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.NumberTheory.Real.Irrational

open Real TensorProduct Module

namespace DehnInvariant

abbrev tensorProduct (G : Type u) (H : Type v) [AddCommGroup G] [AddCommGroup H] :
    Type (max u v) :=
  TensorProduct ℤ G H

def tmul {G : Type u} {H : Type v} [AddCommGroup G] [AddCommGroup H] (g : G) (h : H) :
    tensorProduct G H :=
  TensorProduct.tmul ℤ g h

abbrev DehnGroup := ℝ ⊗[ℤ] (AddCircle (2 * π))

structure Edge where
  length : ℝ
  angle : ℝ

noncomputable def dehnInvariant (edges : List Edge) : DehnGroup :=
  (edges.map (fun e => e.length ⊗ₜ[ℤ] (↑e.angle : AddCircle (2 * π)))).sum

noncomputable def tetrahedralAngle : ℝ := arccos (1 / 3)

def fBar (f : ℝ →ₗ[ℚ] ℝ) (hf_pi : f π = 0) : AddCircle (2 * π) →+ ℝ :=
  QuotientAddGroup.lift (AddSubgroup.zmultiples (2 * π)) f.toAddMonoidHom (by
    intro x hx
    rw [AddMonoidHom.mem_ker]
    obtain ⟨n, hn⟩ := (AddSubgroup.mem_zmultiples_iff).mp hx
    rw [← hn]; change f (n • (2 * π)) = 0
    have h2pi : f (2 * π) = 0 := by
      have : (2 : ℝ) * π = π + π := by ring
      rw [this, map_add, hf_pi, add_zero]
    rw [map_zsmul, h2pi, smul_zero])
