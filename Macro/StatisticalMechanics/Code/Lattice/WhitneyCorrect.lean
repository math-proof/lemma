/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WhitneyCorrect.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.PlanarFaceGeometric.Part5
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanBridgeCycle.Part10
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyCorrect.Part5
open SimpleGraph Set


namespace StatMech

namespace Lattice

macro "whc_prove_inv" : tactic => `(tactic|
  (rename_i a b hab
   have ha : a = ![a 0, a 1] := by funext i; fin_cases i <;> rfl
   have hb : b = ![b 0, b 1] := by funext i; fin_cases i <;> rfl
   rw [hypercubicLattice_adj, Fin.sum_univ_two] at hab
   by_cases h0 : a 0 = b 0
   · rw [ha, hb, h0, whc_shared_hstep, Sym2.eq_iff, Sym2.eq_iff]
     simp only [whc_site_eq_iff, Matrix.cons_val_zero, Matrix.cons_val_one]; omega
   · have h1 : a 1 = b 1 := by omega
     rw [ha, hb, h1, whc_shared_vstep (a 0) (b 0) (b 1) h0, Sym2.eq_iff, Sym2.eq_iff]
     simp only [whc_site_eq_iff, Matrix.cons_val_zero, Matrix.cons_val_one]; omega))


end Lattice
end StatMech
