/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PascalCurves.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.RingTheory.KrullDimension.PID
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Constructions
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Def.v1.Atlas.AlgebraicGeometryI.code.PascalCurves

public section

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

