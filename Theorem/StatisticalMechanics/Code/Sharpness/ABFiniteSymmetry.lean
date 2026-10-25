/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABFiniteSymmetry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.ABFiniteAssembly.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Def.StatisticalMechanics.Code.Sharpness.ABFiniteSymmetry
open Finset Set SimpleGraph


namespace StatMech

namespace Sharpness

open ConfigSpace RandomCurrent

variable {E F : Type*} [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F]

theorem abfs_probV_eq_wprob (p : E -> Real) (A : Set (ConfigSpace E)) :
    probV p A = wprob (abfsLaw p) A := by
  unfold probV wprob configWeightV pweight edgeWeightV abfsLaw
  rfl


theorem abfs_probV_transfer (e : E ≃ F) (p : E -> Real)
    (A : Set (ConfigSpace E)) :
    probV p A =
      probV (fun y => p (e.symm y)) ((cfgEquiv e) ⁻¹' A) := by
  rw [abfs_probV_eq_wprob, abfs_probV_eq_wprob]
  exact wprob_transfer e (abfsLaw p) A

end Sharpness
end StatMech
