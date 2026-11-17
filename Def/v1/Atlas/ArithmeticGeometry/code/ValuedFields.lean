/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ValuedFields.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.MetricSpace.Cauchy
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Topology.Algebra.UniformField

@[expose] public section

open Filter Topology


def SeqConvergesTo {k : Type*} [SeminormedAddCommGroup k] (x : ℕ → k) (ℓ : k) : Prop :=
  Filter.Tendsto x Filter.atTop (nhds ℓ)

def IsCauchySeq (x : ℕ → k) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, ‖x m - x n‖ < ε

def SeqEquiv {k : Type*} [SeminormedAddCommGroup k] (a b : ℕ → k) : Prop :=
  Filter.Tendsto (fun n => a n - b n) Filter.atTop (nhds 0)

def IsCompleteField (k : Type*) [NormedField k] : Prop :=
  ∀ (x : ℕ → k), CauchySeq x → ∃ ℓ : k, Filter.Tendsto x Filter.atTop (nhds ℓ)


