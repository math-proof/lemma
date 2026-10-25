/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourClose2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsSingleCircuit.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsAnchorEncode.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsEulerParity
import Def.StatisticalMechanics.Code.Lattice.PeierlsContourClose2
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

open StatMech.Ising (crossEdges contourLen connClusterFamily bondFinsetTouch)

attribute [local instance] Classical.propDecidable


theorem symPrimal_comm (f g : Site 2) : symPrimal f g = symPrimal g f := by
  classical
  unfold symPrimal
  by_cases h0 : f 0 = g 0
  · rw [if_pos h0, if_pos h0.symm, h0, max_comm]
  · rw [if_neg h0, if_neg (fun hc => h0 hc.symm), max_comm (f 0), min_comm (f 1)]


theorem symPrimal_eq_shared {f g : Site 2} (h : (hypercubicLattice 2).Adj f g) :
    symPrimal f g = sharedPrimalEdge f g := by
  classical
  unfold symPrimal sharedPrimalEdge
  by_cases h0 : f 0 = g 0
  · rw [if_pos h0, if_pos h0]
  · rw [if_neg h0, if_neg h0]
    have hadj := h
    rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
    have h1 : f 1 = g 1 := by
      by_contra hne
      have hb1 : (f 1 - g 1).natAbs ≥ 1 := by omega
      have hb0 : (f 0 - g 0).natAbs ≥ 1 := by
        rcases Int.natAbs_eq (f 0 - g 0) with he | he <;> omega
      omega
    rw [h1, min_self]


end Lattice
end StatMech
