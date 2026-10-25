/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/GridBoxConnected.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneMerge.Part4
import Theorem.StatisticalMechanics.Code.Lattice.SegmentConn
open Set
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


open Classical in


noncomputable def boxEdges (d n : ℕ) : Finset (Sym2 (Site d)) :=
  (((boxFinsetBK d n) ×ˢ (boxFinsetBK d n)).filter
      (fun p => (hypercubicLattice d).Adj p.1 p.2)).image (fun p => s(p.1, p.2))


end Percolation
end StatMech
