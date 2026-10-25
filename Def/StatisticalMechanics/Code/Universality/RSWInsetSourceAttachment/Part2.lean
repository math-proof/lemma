/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetSourceAttachment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWStrictAxisSourcePartition
import Abbrev.StatisticalMechanics.Code.Universality.RSWInsetSourceAttachment
open Finset SimpleGraph Set MeasureTheory


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def rlc_insetRightSourceCoreEvent (n : Int) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  rlc_lrRestrictedEvent 1 (2 * n) (-n) n
    rlc_strictLowerHalf rlc_upperHalf


noncomputable def rlc_insetRightHom (n : Int) :
    ((hypercubicLattice 2).induce (rect 1 (2 * n) (-n) n)) →g
      ((hypercubicLattice 2).induce (rect 0 (2 * n) (-n) n)) where
  toFun z := ⟨z, by
    have hz := z.2
    rw [mem_rect] at hz ⊢
    omega⟩
  map_rel' := by
    intro a b hab
    exact hab

end
end StatMech.Universality
