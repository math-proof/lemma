/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FiniteRangePerco.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.InhomogeneousProduct.Part2
import Theorem.StatisticalMechanics.Code.Percolation.SubcriticalDecayFull.Part2
import Theorem.StatisticalMechanics.Code.Percolation.SurfaceReassembly
import Theorem.StatisticalMechanics.Code.Sharpness.BkCriterionFull.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.FiniteRangePerco.Part11
open MeasureTheory
open scoped NNReal


namespace StatMech

namespace Sharpness

open ConfigSpace Lattice Percolation


variable {d : ℕ}


def frpTranslateHom (K : FiniteRangeKernel d)
    (g : Multiplicative (Site d)) (omega : ConfigSpace (Sym2 (Site d))) :
    openSub (frpGraph K) omega →g openSub (frpGraph K) (shift g omega) where
  toFun x := g • x
  map_rel' {x y} h := (frp_openSub_adj_shift K g omega x y).mpr h

def frpTranslateHomInv (K : FiniteRangeKernel d)
    (g : Multiplicative (Site d)) (omega : ConfigSpace (Sym2 (Site d))) :
    openSub (frpGraph K) (shift g omega) →g openSub (frpGraph K) omega where
  toFun x := g⁻¹ • x
  map_rel' {x y} h := by
    have h' := (frp_openSub_adj_shift K g omega (g⁻¹ • x) (g⁻¹ • y)).mp
    simp only [smul_inv_smul] at h'
    exact h' h


end Sharpness
end StatMech
