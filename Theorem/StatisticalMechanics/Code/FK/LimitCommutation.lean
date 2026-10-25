/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/LimitCommutation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.MultiEdgeDecay.Part4
import Def.StatisticalMechanics.Code.FK.LimitCommutation
open MeasureTheory Filter Topology SimpleGraph Set
open StatMech.ConfigSpace StatMech.Lattice
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false


namespace StatMech

namespace FK

open StatMech.IsingFK StatMech.Percolation

variable {d : ℕ}


theorem lmc_transEdgeIncl_sigma_eq_smul (d m : ℕ) (v : Site d) (eb : Sym2 (boxVerts d m)) :
    lmc_transEdgeIncl d m v (Sym2.map (fvs_transEquiv d m v) eb)
      = (Multiplicative.ofAdd v) • (edgeIncl d m eb) := by
  unfold lmc_transEdgeIncl edgeIncl
  show Sym2.map _ (Sym2.map _ eb) = Sym2.map _ (Sym2.map _ eb)
  rw [Sym2.map_map, Sym2.map_map]
  congr 1
  funext x
  show (fvs_transEquiv d m v x : Site d) = Multiplicative.ofAdd v • (x : Site d)
  rw [fvs_transEquiv_val]
  show (x : Site d) + v = v + (x : Site d)
  rw [add_comm]


theorem lmc_transImage_eq_smulImage (d m : ℕ) (v : Site d) (t : Finset (Sym2 (boxVerts d m))) :
    (t.image (Sym2.map (fvs_transEquiv d m v))).image (lmc_transEdgeIncl d m v)
      = (t.image (edgeIncl d m)).image (fun e => (Multiplicative.ofAdd v) • e) := by
  rw [Finset.image_image, Finset.image_image]
  refine Finset.image_congr fun eb _ => ?_
  simp only [Function.comp_apply]
  exact lmc_transEdgeIncl_sigma_eq_smul d m v eb


end FK
end StatMech
