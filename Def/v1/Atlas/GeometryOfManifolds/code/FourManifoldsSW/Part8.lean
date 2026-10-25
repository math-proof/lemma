/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/FourManifoldsSW.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup
import Mathlib.Topology.VectorBundle.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Complex.Circle
import Theorem.v1.Atlas.GeometryOfManifolds.code.FourManifoldsSW.Part2
open Manifold

set_option autoImplicit false


noncomputable section

noncomputable section SpinCGroupSection

/-- The equivalence relation defining $\mathrm{Spin}^c(4) = (\mathrm{Spin}(4) \times S^1)/\{\pm 1\}$
on pairs $(p, z) \in \mathrm{Spin}(Q) \times S^1$: $(p, z) \sim (-p, -z)$. -/
def SpinCGroupRel (Q : QuadraticForm ℝ (Fin 4 → ℝ)) :
    (spinGroup Q) × Circle → (spinGroup Q) × Circle → Prop :=
  fun p q => p = q ∨
    (∃ (h : (-↑p.1.1 : CliffordAlgebra Q) ∈ spinGroup Q),
      q.1 = ⟨-↑p.1.1, h⟩ ∧ q.2 = negOneCircle * p.2)

/-- The Spin-c group $\mathrm{Spin}^c(Q) = (\mathrm{Spin}(Q) \times S^1)/\{\pm 1\}$. -/
def SpinCGroup (Q : QuadraticForm ℝ (Fin 4 → ℝ)) :=
  Quot (SpinCGroupRel Q)

/-- The canonical projection $\mathrm{Spin}(Q) \times S^1 \to \mathrm{Spin}^c(Q)$. -/
def SpinCGroup.mk (Q : QuadraticForm ℝ (Fin 4 → ℝ)) :
    spinGroup Q × Circle → SpinCGroup Q :=
  Quot.mk _

/-- The determinant homomorphism $\det : \mathrm{Spin}^c(Q) \to S^1$, $[p, z] \mapsto z^2$,
well-defined modulo $\{\pm 1\}$. -/
def SpinCGroup.det (Q : QuadraticForm ℝ (Fin 4 → ℝ)) :
    SpinCGroup Q → Circle :=
  Quot.lift (fun p => p.2 * p.2) (by
    intro a b hab
    rcases hab with rfl | ⟨_, _, hq2⟩
    · rfl
    · simp only [hq2]
      rw [mul_mul_mul_comm negOneCircle a.2 negOneCircle a.2]
      rw [← sq, ← sq, negOneCircle_sq, one_mul])

end SpinCGroupSection
end
