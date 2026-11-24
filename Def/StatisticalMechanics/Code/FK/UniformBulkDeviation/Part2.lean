module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.FK.SpatialCollapse
public import Theorem.StatisticalMechanics.Code.FK.OneSidedContinuity
public import Theorem.StatisticalMechanics.Code.FK.WiredPressureDeriv.Part4
public import Theorem.StatisticalMechanics.Code.FK.FKDensityDeriv.Part2
public import Theorem.StatisticalMechanics.Code.FK.FKUniquenessClose3
public import Theorem.StatisticalMechanics.Code.FK.FKLimitsClose.Part3
public import Theorem.StatisticalMechanics.Code.FK.UniformBulkDeviation
open MeasureTheory Set Filter Topology Real
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.openClassical false
set_option linter.style.setOption false


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/UniformBulkDeviation.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace FK

open ConfigSpace StatMech.Lattice

variable {d : ℕ}


def ubd_FreeUniformBulkDeviation (N : ℕ) : Prop :=
  ∀ (e' : Sym2 (boxVerts d N)) (t : ℝ),
    ∃ (In : (n : ℕ) → Finset (Sym2 (boxVerts d n))) (δ : ℕ → ℝ),
      (∀ n, In n ⊆ (boxGraph d n).edgeFinset) ∧
      (∀ n, 0 ≤ δ n) ∧ Tendsto δ atTop (𝓝 0) ∧
      (∀ n, ∀ e ∈ In n,
        |edgeMargProb (fkProb (boxGraph d n) (fsc_logistic t) 2) e
          - freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t)| ≤ δ n) ∧
      Tendsto (fun n =>
        (((boxGraph d n).edgeFinset.card - (In n).card : ℝ)) / (boxGraph d n).edgeFinset.card)
        atTop (𝓝 0)


def ubd_WiredUniformBulkDeviation (N : ℕ) : Prop :=
  ∀ (e' : Sym2 (boxVerts d N)) (t : ℝ),
    ∃ (In : (n : ℕ) → Finset (Sym2 (boxVerts d n))) (δ : ℕ → ℝ),
      (∀ n, In n ⊆ (boxGraph d n).edgeFinset) ∧
      (∀ n, 0 ≤ δ n) ∧ Tendsto δ atTop (𝓝 0) ∧
      (∀ n, ∀ e ∈ In n,
        |edgeMargProb (wiredFkProb (boxGraph d n) (boxBoundary d n) (fsc_logistic t) 2) e
          - wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t)| ≤ δ n) ∧
      Tendsto (fun n =>
        (((boxGraph d n).edgeFinset.card - (In n).card : ℝ)) / (boxGraph d n).edgeFinset.card)
        atTop (𝓝 0)


end FK
end StatMech
