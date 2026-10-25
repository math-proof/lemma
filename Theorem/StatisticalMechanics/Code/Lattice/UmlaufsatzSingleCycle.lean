/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzSingleCycle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartInjective
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Lattice.TurningNumber.Part6
import Theorem.StatisticalMechanics.Code.Lattice.CornerBalance.Part4
import Theorem.StatisticalMechanics.Code.Lattice.EarRemoval.Part5
import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
import Theorem.StatisticalMechanics.Code.Lattice.OrbitEncloses.Part4
import Theorem.StatisticalMechanics.Code.Lattice.JordanSingleCycle.Part4
import Theorem.StatisticalMechanics.Code.Lattice.Umlaufsatz.Part4
import Def.StatisticalMechanics.Code.Lattice.UmlaufsatzSingleCycle
open SimpleGraph Function Set Finset


namespace StatMech

namespace Lattice

open StatMech.Percolation (origin)

variable {ω : ConfigSpace (Sym2 (Site 2))}


theorem usc_dir_mem_fourDirs (e : Dart) : e.dir ∈ usc_fourDirs := by
  unfold usc_fourDirs
  rcases dartDir_cases e with h | h | h | h <;> rw [h] <;> simp


theorem usc_fourDirs_card : usc_fourDirs.card = 4 := by
  unfold usc_fourDirs
  decide


theorem usc_dir_injOn_of_face_eq (f : Site 2) (T : Set Dart) (hT : ∀ e ∈ T, dartFace e = f) :
    Set.InjOn (fun e : Dart => e.dir) T := by
  intro e₁ he₁ e₂ he₂ hdir
  simp only at hdir
  exact dartFace_eq_of_dir_eq hdir (by rw [hT e₁ he₁, hT e₂ he₂])


end Lattice
end StatMech
