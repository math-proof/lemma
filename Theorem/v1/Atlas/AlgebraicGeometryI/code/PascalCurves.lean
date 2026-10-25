/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PascalCurves.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.KrullDimension.PID
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Constructions
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.PascalCurves


/-- The cofinite equivalence map is continuous in the cofinite topologies. -/
lemma cofinite_continuous_of_equiv (X Y : Type*) (e : X ≃ Y) :
    Continuous (cofiniteEquiv X Y e) := by
  rw [continuous_def]
  intro s hs
  rw [CofiniteTopology.isOpen_iff'] at hs ⊢
  rcases hs with rfl | hfin
  · simp [Set.preimage_empty]
  · right
    rw [← Set.preimage_compl]
    exact Set.Finite.preimage ((cofiniteEquiv X Y e).injective.injOn) hfin

