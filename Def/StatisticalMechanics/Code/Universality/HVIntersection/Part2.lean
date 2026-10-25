/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HVIntersection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.TwoDim.Crossings.Part4
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.RSW.Strip.Part2
import Theorem.StatisticalMechanics.Code.Universality.Defs.Part7
import Theorem.StatisticalMechanics.Code.Universality.RSWStrip.Part3
import Theorem.StatisticalMechanics.Code.Universality.HVIntersection
open Set MeasureTheory SimpleGraph
open scoped ENNReal NNReal


namespace StatMech

namespace Universality

open StatMech.Lattice

open StatMech.RSW.Box

open StatMech.RSW.Strip


def overlapComp (ω : ConfigSpace (Sym2 (Site 2))) (m m' c d : ℤ)
    (xB : Site 2) (hxB : xB ∈ rect m m' c d) : Set (Site 2) :=
  {z | ∃ hz : z ∈ rect m m' c d, ConnectedWithin 2 ω (rect m m' c d) ⟨xB, hxB⟩ ⟨z, hz⟩}


def VSeparatesH (ω : ConfigSpace (Sym2 (Site 2))) (α β m m' c d : ℤ) : Prop :=
  α ≤ m → m ≤ m' → m' ≤ β →
  ∀ (xB : Site 2) (hxB : xB ∈ rect m m' c d),
  ∀ (x y : rect α β c d), (x : Site 2) 0 = α → (y : Site 2) 0 = β →
  ∀ (w : (openSubgraphInduce 2 ω (rect α β c d)).Walk x y),
    ∃ z ∈ w.support, (z : Site 2) ∈ overlapComp ω m m' c d xB hxB


end Universality
end StatMech
