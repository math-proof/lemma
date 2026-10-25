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
open Set MeasureTheory SimpleGraph
open scoped ENNReal NNReal


namespace StatMech

namespace Universality

open StatMech.Lattice

open StatMech.RSW.Box

open StatMech.RSW.Strip


def HVMeetProperty (ω : ConfigSpace (Sym2 (Site 2))) (α β m m' c d : ℤ) : Prop :=
  α ≤ m → m ≤ m' → m' ≤ β →
  ∀ (xL : leftSide α β c d) (yR : rightSide α β c d),
    ConnectedWithin 2 ω (rect α β c d)
      ⟨(xL : Site 2), leftSide_subset xL.2⟩ ⟨(yR : Site 2), rightSide_subset yR.2⟩ →
  ∀ (xB : bottomSide m m' c d) (yT : topSide m m' c d),
    ConnectedWithin 2 ω (rect m m' c d)
      ⟨(xB : Site 2), bottomSide_subset xB.2⟩ ⟨(yT : Site 2), topSide_subset yT.2⟩ →
  ∃ (z : Site 2) (hzO : z ∈ rect m m' c d) (hzH : z ∈ rect α β c d),
    ConnectedWithin 2 ω (rect α β c d)
        ⟨(xL : Site 2), leftSide_subset xL.2⟩ ⟨z, hzH⟩ ∧
    ConnectedWithin 2 ω (rect m m' c d)
        ⟨(xB : Site 2), bottomSide_subset xB.2⟩ ⟨z, hzO⟩


end Universality
end StatMech
