/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Morphisms.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ArithmeticGeometry.code.ProjectiveVarieties.Part7
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.ProjectiveVarieties
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.Varieties
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.VarietyAlgebraEquiv
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.Theorem1324
import Def.v1.Atlas.ArithmeticGeometry.code.Varieties.Part9
import Theorem.v1.Atlas.ArithmeticGeometry.code.VarietyAlgebraEquiv.Part2
import Theorem.v1.Atlas.ArithmeticGeometry.code.Theorem1324
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.Basic
import Mathlib.Topology.Order
import Theorem.v1.Atlas.ArithmeticGeometry.code.Morphisms.Part2


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
