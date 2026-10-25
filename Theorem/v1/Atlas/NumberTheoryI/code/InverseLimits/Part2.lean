/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/InverseLimits.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.UniformSpace.Completion
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Constructions
import Mathlib.Order.DirectedInverseSystem
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Topology.Algebra.OpenSubgroup
import Abbrev.v1.Atlas.NumberTheoryI.code.InverseLimits.Part2


noncomputable section

open Set

example {ι : Type*} [Preorder ι] {F : ι → Type*}
    {f : ∀ ⦃i j : ι⦄, i ≤ j → F j → F i} [InverseSystem f] :
    (∀ (i : ι) (x : F i), f le_rfl x = x) ∧
    (∀ ⦃k j i : ι⦄ (hkj : k ≤ j) (hji : j ≤ i) (x : F i),
      f hkj (f hji x) = f (hkj.trans hji) x) :=
  ⟨InverseSystem.map_self, InverseSystem.map_map⟩

end
