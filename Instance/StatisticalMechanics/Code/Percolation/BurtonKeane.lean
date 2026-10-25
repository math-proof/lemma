/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeane.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.Theta
import Theorem.StatisticalMechanics.Code.Foundations.Ergodicity.Part2
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane
open MeasureTheory

set_option linter.style.show false


namespace StatMech

namespace Percolation

open StatMech.Lattice StatMech.ConfigSpace

variable {d : ℕ}


noncomputable instance sym2Action (d : ℕ) :
    MulAction (Multiplicative (Site d)) (Sym2 (Site d)) where
  smul g e := Sym2.map (fun x => g • x) e
  one_smul e := by
    show Sym2.map _ e = e
    have h : (fun x : Site d => (1 : Multiplicative (Site d)) • x) = id := by
      funext x; rw [one_smul]; rfl
    rw [h, Sym2.map_id]; rfl
  mul_smul g h e := by
    show Sym2.map _ e = Sym2.map _ (Sym2.map _ e)
    rw [Sym2.map_map]
    congr 1
    funext x
    show (g * h) • x = g • h • x
    rw [mul_smul]


end Percolation
end StatMech
