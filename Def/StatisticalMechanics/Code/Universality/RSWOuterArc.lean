/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWOuterArc.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWArcSupport
import Theorem.StatisticalMechanics.Code.Universality.RSWGapSymmetry.Part4
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box


noncomputable def rlc_orderedContourArc {H : SimpleGraph (Site 2)}
    {u x y : Site 2} (c : H.Walk u u)
    (hx : x ∈ c.support) (hy : y ∈ c.support) : H.Walk x y :=
  (c.rotate x hx).takeUntil y
    ((SimpleGraph.Walk.mem_support_rotate_iff c x hx).2 hy)


noncomputable def rlc_complementaryContourArc {H : SimpleGraph (Site 2)}
    {u x y : Site 2} (c : H.Walk u u)
    (hx : x ∈ c.support) (hy : y ∈ c.support) : H.Walk x y :=
  ((c.rotate x hx).dropUntil y
    ((SimpleGraph.Walk.mem_support_rotate_iff c x hx).2 hy)).reverse


end Universality
end StatMech
