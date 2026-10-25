/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/LatticeMengerAttach.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationExistence2.Part3
import Theorem.StatisticalMechanics.Code.Percolation.BoxMengerAttachment.Part3
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


noncomputable def lma_corridorEdges (j : Fin d) (L : ℕ) : Finset (Sym2 (Site d)) :=
  (Finset.range L).image
    (fun t : ℕ => s(hrHD_rayPt j ((t : ℤ) + 1), hrHD_rayPt j ((t : ℤ) + 2)))


end Percolation
end StatMech
