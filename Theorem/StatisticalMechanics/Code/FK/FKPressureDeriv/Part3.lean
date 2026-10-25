/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKPressureDeriv.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.FKUniquenessSkeleton.Part3
import Theorem.StatisticalMechanics.Code.FK.SuperMultiplicative.Part4
import Theorem.StatisticalMechanics.Code.FK.FeketeLimit
import Theorem.StatisticalMechanics.Code.FK.ConvexDerivLimit
import Theorem.StatisticalMechanics.Code.FK.IVPressureConvex.Part5
import Theorem.StatisticalMechanics.Code.FK.RussoDerivativeBeta.Part4
import Theorem.StatisticalMechanics.Code.FK.DensityFiniteToInfinite.Part2
import Def.StatisticalMechanics.Code.FK.FKPressureDeriv.Part2
open MeasureTheory Set Filter Topology Real
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace FK

open ConfigSpace StatMech.Lattice


variable {d : ℕ}


variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


theorem fpd_freeDensity_at_diff_of_collapse (d N : ℕ)
    (Gn : ℕ → SimpleGraph (boxVerts d N)) [∀ n, DecidableRel (Gn n).Adj]
    (hE : ∀ n, 0 < (Gn n).edgeFinset.card)
    (g : ℝ → ℝ) (hg : ConvexOn ℝ univ g)
    (hlim : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (Gn n) 2 t) atTop (𝓝 (g t)))
    (hcol : fpd_AvgDensityCollapse d N Gn)
    (e' : Sym2 (boxVerts d N)) (t : ℝ)
    (hdiff : pressureLeftDeriv g t = pressureRightDeriv g t) :
    freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) = pressureLeftDeriv g t := by
  have hderiv := fpd_ivPressureDeriv_eq_avgDensity_limit Gn hE g hg hlim t hdiff
  rw [hdiff]
  exact tendsto_nhds_unique (hcol e' t) hderiv


end FK
end StatMech
