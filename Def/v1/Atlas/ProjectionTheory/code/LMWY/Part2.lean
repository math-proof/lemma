/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/LMWY.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.v1.Atlas.ProjectionTheory.code.LMWY
open Matrix


namespace HomogeneousDynamics

/-- The unipotent element $U(t)$ packaged as an element of $SL(3, \mathbb{R})$ using
the determinant computation. -/
noncomputable def unipotentElem (t : ℝ) : SpecialLinearGroup (Fin 3) ℝ :=
  ⟨unipotentU t, unipotentU_det t⟩

/-- A subset `S` of a pseudometric space is `ε`-dense if every point lies within distance
`ε` of some element of `S`. -/
def IsEpsDense {X : Type*} [PseudoMetricSpace X] (S : Set X) (ε : ℝ) : Prop :=
  ∀ x : X, ∃ s ∈ S, dist x s ≤ ε

/-- The orbit segment $\{U(t) \cdot x : t \in [0, T]\}$ of a point $x$ in the homogeneous
space $SL(3,\mathbb{R}) / SL(3,\mathbb{Z})$ under the unipotent flow. -/
noncomputable def orbitSegment
    (x : SpecialLinearGroup (Fin 3) ℝ ⧸ SL3Z)
    (T : ℝ) : Set (SpecialLinearGroup (Fin 3) ℝ ⧸ SL3Z) :=
  (fun t => unipotentElem t • x) '' (Set.Icc 0 T)

end HomogeneousDynamics
