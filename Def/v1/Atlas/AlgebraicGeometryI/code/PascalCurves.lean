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

