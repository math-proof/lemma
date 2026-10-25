/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/MatchedPlanarDualityClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.RSW.SelfDuality.Part2
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.JordanContour.Part3
import Theorem.StatisticalMechanics.Code.Lattice.SegmentConn
import Theorem.StatisticalMechanics.Code.Universality.DualEventSetEquality.Part4
import Theorem.StatisticalMechanics.Code.Universality.BoxCrossingDichotomy
import Theorem.StatisticalMechanics.Code.Universality.BoxCrossingDichotomyClose.Part3
import Theorem.StatisticalMechanics.Code.Universality.JordanExhaustivityClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.RSWFrameReconcileClose.Part3
import Theorem.StatisticalMechanics.Code.Universality.MatchedPlanarDualityClose.Part2
open Set SimpleGraph Finset
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

def mpd_leftReach (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) : Set (Site 2) :=
  {v | v ∈ rect 0 (n + 1) 0 n ∧ ∃ (x : Site 2) (hx : x ∈ leftSide 0 (n + 1) 0 n)
      (hv : v ∈ rect 0 (n + 1) 0 n),
      ConnectedWithin 2 ω (rect 0 (n + 1) 0 n) ⟨x, leftSide_subset hx⟩ ⟨v, hv⟩}

end Universality
end StatMech
