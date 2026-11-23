/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/CompleteFields.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.UniformSpace.Completion
public import Mathlib.Topology.UniformSpace.AbstractCompletion
public import Mathlib.Topology.Algebra.UniformField
public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Analysis.Normed.Ring.WithAbs
public import Mathlib.Analysis.AbsoluteValue.Equivalence
public import Mathlib.NumberTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.Ideal.IntegralClosure
public import Mathlib.RingTheory.Ideal.Over
public import Def.v1.Atlas.NumberTheoryI.code.Chapter1.AbsoluteValues.Part2
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.Chapter1.AbsoluteValues

@[expose] public section

noncomputable section

open scoped Topology

open UniformSpace

def Converges {X : Type*} [PseudoMetricSpace X] (u : ℕ → X) : Prop :=
  ∃ x : X, Filter.Tendsto u Filter.atTop (nhds x)

end
