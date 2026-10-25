/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalFields.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.Analysis.Normed.Field.ProperSpace
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Analysis.Normed.Algebra.GelfandMazur
import Mathlib.RingTheory.LaurentSeries
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.NumberTheory.Ostrowski
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.NumberTheory.Padics.WithVal
import Mathlib.Topology.Algebra.UniformRing
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Def.v1.Atlas.NumberTheoryI.code.Adeles.Part10
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.Adeles
import Instance.v1.Atlas.NumberTheoryI.code.LocalFields
open Metric Filter Set Topology

attribute [instance] IsLocalField.locallyCompact


lemma not_accPt_of_separated {X : Type*} [MetricSpace X] {S : Set X}
    (h_sep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ dist x y) (a : X) :
    ¬ AccPt a (𝓟 S) := by
  intro hacc; rw [accPt_iff_nhds] at hacc
  obtain ⟨y₁, ⟨hy₁_ball, hy₁_S⟩, hy₁_ne⟩ :=
    hacc (ball a (1/2)) (ball_mem_nhds a (by positivity))
  obtain ⟨y₂, ⟨hy₂_ball, hy₂_S⟩, _⟩ :=
    hacc (ball a (1/2) \ {y₁}) (by
      apply diff_mem (ball_mem_nhds a (by positivity))
      exact isOpen_ne.mem_nhds (Ne.symm hy₁_ne))
  linarith [h_sep y₁ hy₁_S y₂ hy₂_S (Ne.symm (fun h => hy₂_ball.2 (mem_singleton_iff.mpr h))),
            dist_triangle y₁ a y₂, mem_ball.mp hy₁_ball, mem_ball.mp hy₂_ball.1, dist_comm a y₂]

