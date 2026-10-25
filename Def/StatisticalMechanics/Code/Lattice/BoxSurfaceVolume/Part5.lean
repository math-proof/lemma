/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BoxSurfaceVolume.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part4
open Set Finset Filter Topology


namespace StatMech

namespace Lattice

noncomputable def boxSV_edgeCard (d n : ℕ) : ℕ := (boxSV_edgeF d n).card


noncomputable def boxSV_fwdDom (d n : ℕ) (hd : 1 ≤ d) : Finset (Site d) :=
  (boxSV_boxF d n).filter (fun x => x ⟨0, hd⟩ + 1 ∈ Finset.Icc (-(n : ℤ)) n)


end Lattice
end StatMech
