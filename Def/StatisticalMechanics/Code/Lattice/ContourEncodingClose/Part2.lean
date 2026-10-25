/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourEncodingClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.ClusterContourBijection.Part4
import Theorem.StatisticalMechanics.Code.Lattice.CanonicalContour.Part6
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.ContourEncodingClose
open Set Finset SimpleGraph
open StatMech.Ising


namespace StatMech

namespace Lattice

attribute [local instance] Classical.propDecidable

variable {d : ℕ}


noncomputable def ccb_anchorRow (ℓ : ℕ) : Finset (Site 2) :=
  (Finset.range ℓ).image (fun j : ℕ => (![ (j : ℤ), 0] : Site 2))


end Lattice
end StatMech
