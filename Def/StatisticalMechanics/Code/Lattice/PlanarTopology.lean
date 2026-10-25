/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PlanarTopology.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Instance.StatisticalMechanics.Code.Lattice.PlanarTopology
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

def shift (d : ℕ) (x : Site d) (j : Fin d) (s : ℤ) : Site d :=
  Function.update x j (x j + s)


def candMap (d : ℕ) (x : Site d) : Fin d × Bool → Site d :=
  fun p => shift d x p.1 (if p.2 then 1 else -1)


def candFinset (d : ℕ) (x : Site d) : Finset (Site d) :=
  Finset.univ.image (candMap d x)


end Lattice
end StatMech
