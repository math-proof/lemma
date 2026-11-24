module
public import Mathlib.Topology.Algebra.Valued.LocallyCompact
public import Mathlib.Analysis.Normed.Field.ProperSpace
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.Analysis.Normed.Algebra.GelfandMazur
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.NumberTheory.Ostrowski
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.NumberTheory.Padics.WithVal
public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.RingTheory.Valuation.Discrete.RankOne
public import Def.v1.Atlas.NumberTheoryI.code.Adeles.Part10
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.Adeles
public import Instance.v1.Atlas.NumberTheoryI.code.LocalFields
open Metric Filter Set Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalFields.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

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

