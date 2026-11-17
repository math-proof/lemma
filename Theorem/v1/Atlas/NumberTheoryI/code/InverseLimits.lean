/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/InverseLimits.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Topology.UniformSpace.Completion
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Separation.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Order.DirectedInverseSystem
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Abbrev.v1.Atlas.NumberTheoryI.code.InverseLimits

public section

noncomputable section

open Set

example (I : Type*) [PartialOrder I] [IsDirected I (· ≤ ·)] [Nonempty I] :
    ∀ a b : I, ∃ c, a ≤ c ∧ b ≤ c := directed_of (· ≤ ·)

end
