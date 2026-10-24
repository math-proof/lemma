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

/-- Equivalence between cofinite topologies induced by an underlying type equivalence. -/
noncomputable def cofiniteEquiv (X Y : Type*) (e : X ≃ Y) :
    CofiniteTopology X ≃ CofiniteTopology Y :=
  (CofiniteTopology.of (X := X)).symm.trans (e.trans (CofiniteTopology.of (X := Y)))

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

/-- A type equivalence promotes to a homeomorphism between cofinite topologies. -/
noncomputable def cofiniteHomeomorph (X Y : Type*) (e : X ≃ Y) :
    CofiniteTopology X ≃ₜ CofiniteTopology Y where
  toEquiv := cofiniteEquiv X Y e
  continuous_toFun := cofinite_continuous_of_equiv X Y e
  continuous_invFun := by
    show Continuous (cofiniteEquiv X Y e).invFun
    have : (cofiniteEquiv X Y e).invFun = (cofiniteEquiv Y X e.symm).toFun := by
      ext x; simp [cofiniteEquiv, CofiniteTopology.of]
    rw [this]
    exact cofinite_continuous_of_equiv Y X e.symm

/-- Any two irreducible affine curves over an algebraically closed field are
homeomorphic in the Zariski topology, since both are countably infinite cofinite
topological spaces. -/
