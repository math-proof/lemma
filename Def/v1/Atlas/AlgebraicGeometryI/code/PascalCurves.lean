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

@[expose] public section

/-- Equivalence between cofinite topologies induced by an underlying type equivalence. -/
noncomputable def cofiniteEquiv (X Y : Type*) (e : X ≃ Y) :
    CofiniteTopology X ≃ CofiniteTopology Y :=
  (CofiniteTopology.of (X := X)).symm.trans (e.trans (CofiniteTopology.of (X := Y)))

