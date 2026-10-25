/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineMetric.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.Building.Affine.Part2
import Def.v1.Atlas.Buildings.code.AffineCoxeter.CanonicalMetric.Part2
import Lemma.Real.IsWInvariantEuclideanDist
import Mathlib.Topology.MetricSpace.Basic
import Def.v1.Atlas.Buildings.code.Building.AffineMetric.Part2
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

open Classical
open ChamberComplex
open AffineCoxeter


/-- Per-apartment metric data for a building: an ambient space $X$ with
embedding $\iota : V \to X$ and a per-apartment pseudo-distance
$\mathrm{dist}_{\mathrm{fn}}$ that is symmetric, satisfies the triangle
inequality, vanishes on the diagonal, is preserved by every simplicial
isomorphism between apartments, and normalizes each chamber to have
diameter $1$. -/
structure ApartmentMetricData (b : Building V) where
  X : Type*
  ι : V → X
  dist_X : X → X → ℝ
  dist_fn : { A : SimplicialComplex V // A ∈ b.apartmentSystem.apartments } → (V → V → ℝ)
  dist_nonneg : ∀ A x y, 0 ≤ dist_fn A x y
  dist_symm : ∀ A x y, dist_fn A x y = dist_fn A y x
  dist_eq_zero : ∀ A (x : V), dist_fn A x x = 0
  dist_triangle : ∀ A x y z, dist_fn A x z ≤ dist_fn A x y + dist_fn A y z
  iso_isometry : ∀ (A₁ A₂ : { A // A ∈ b.apartmentSystem.apartments }),
    ∀ (φ : SimplicialMap A₁.val A₂.val),
      (∀ s ∈ A₁.val.faces, s.image φ.toFun ∈ A₂.val.faces) →
      ∀ x y, dist_fn A₁ x y = dist_fn A₂ (φ.toFun x) (φ.toFun y)
  chamber_diam_one : ∀ (A : { A // A ∈ b.apartmentSystem.apartments }),
    ∀ C, A.val.IsMaximal C →
      (∀ x ∈ C, ∀ y ∈ C, dist_fn A x y ≤ 1) ∧
      (∃ x ∈ C, ∃ y ∈ C, dist_fn A x y = 1)

