/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetLeftSourceAttachment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWInsetSourceAttachment.Part2
import Abbrev.StatisticalMechanics.Code.Universality.RSWInsetLeftSourceAttachment
open Finset SimpleGraph Set MeasureTheory


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable def rlc_insetLeftHom (n : Int) :
    ((hypercubicLattice 2).induce (rect (-2 * n) (-1) (-n) n)) →g
      ((hypercubicLattice 2).induce (rect (-2 * n) 0 (-n) n)) where
  toFun z := ⟨z, by
    have hz:=z.2
    rw [mem_rect] at hz ⊢
    omega⟩
  map_rel' := by intro a b h; exact h

end
end StatMech.Universality
