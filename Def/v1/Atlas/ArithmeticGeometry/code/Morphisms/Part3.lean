module
public import Def.v1.Atlas.ArithmeticGeometry.code.ProjectiveVarieties.Part7
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.ProjectiveVarieties
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.Varieties
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.VarietyAlgebraEquiv
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.Theorem1324
public import Def.v1.Atlas.ArithmeticGeometry.code.Varieties.Part9
public import Theorem.v1.Atlas.ArithmeticGeometry.code.VarietyAlgebraEquiv.Part2
public import Theorem.v1.Atlas.ArithmeticGeometry.code.Theorem1324
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Order
public import Theorem.v1.Atlas.ArithmeticGeometry.code.Morphisms.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Morphisms.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

open MvPolynomial

variable (k : Type*) [Field k]

/-- The *projective Zariski topology* on $\mathbb{P}^n(\bar k)$: closed sets
are exactly the projectively algebraic subsets. -/
@[reducible]
def zariskiTopologyProjective (n : ℕ) : TopologicalSpace (ProjectiveSpace_k k n) :=
  TopologicalSpace.ofClosed (projAlgSetsCollection k n)
    (projAlgSets_empty_mem k n)
    (projAlgSets_sInter_mem k n)
    (projAlgSets_union_mem k n)

end
