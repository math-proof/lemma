/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/CompleteFields.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.UniformSpace.Completion
import Mathlib.Topology.UniformSpace.AbstractCompletion
import Mathlib.Topology.Algebra.UniformField
import Mathlib.Topology.Algebra.UniformRing
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Normed.Ring.WithAbs
import Mathlib.Analysis.AbsoluteValue.Equivalence
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Ideal.Over
import Def.v1.Atlas.NumberTheoryI.code.Chapter1.AbsoluteValues.Part2
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.Chapter1.AbsoluteValues
import Theorem.v1.Atlas.NumberTheoryI.code.CompleteFields


noncomputable section

open scoped Topology

open UniformSpace

@[reducible]
def AbsoluteValue.inducedTopology {K : Type*} [Field K] (v : AbsoluteValue K ℝ) :
    TopologicalSpace K :=
  letI : NormedRing (WithAbs v) := WithAbs.normedRing v
  TopologicalSpace.induced (WithAbs.toAbs v) inferInstance

def DiscreteValuation.ExtendsWithIndex
    {K : Type*} [Field K]
    {L : Type*} [Field L] [Algebra K L]
    (w : Valuation L (WithZero (Multiplicative ℤ)))
    (v : Valuation K (WithZero (Multiplicative ℤ)))
    (e : ℕ) : Prop :=
  0 < e ∧ ∀ x : K, w (algebraMap K L x) = (v x) ^ e

end
