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
open MeasureTheory Set Filter Topology Real
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace FK

open ConfigSpace StatMech.Lattice


variable {d : ℕ}


theorem fpd_exists_convex_ivPressure
    {W : Type*} [Fintype W] [DecidableEq W]
    (Gn : ℕ → SimpleGraph W) [∀ i, DecidableRel (Gn i).Adj]
    (hE : ∀ n, 0 < (Gn n).edgeFinset.card)
    (hjux : ∀ m n, Gn (m + n) ≃g Gn m ⊕g Gn n)
    (hbdd : ∀ t, BddBelow (Set.range fun n =>
      (-Real.log (fkZ (Gn n) (fsc_logistic t) 2)) / n))
    (c : ℝ → ℝ) (hc : ∀ t, c t ≠ 0)
    (he : ∀ t, Tendsto (fun n => ((Gn n).edgeFinset.card : ℝ) / n) atTop (𝓝 (c t))) :
    ∃ g : ℝ → ℝ,
      (∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (Gn n) 2 t) atTop (𝓝 (g t)))
        ∧ ConvexOn ℝ univ g :=
  fsm_fekete_limit Gn 2 (by norm_num) hE hjux hbdd c hc he


theorem fpd_ivPressure_convexDeriv_facts
    {W : Type*} [Fintype W] [DecidableEq W]
    (Gn : ℕ → SimpleGraph W) [∀ i, DecidableRel (Gn i).Adj]
    (hconv : ∀ n, ConvexOn ℝ univ (ivp2_tiltFreeEnergy (Gn n) 2))
    (g : ℝ → ℝ)
    (hlim : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (Gn n) 2 t) atTop (𝓝 (g t))) :
    ConvexOn ℝ univ g
      ∧ (∀ t, HasDerivWithinAt g (pressureRightDeriv g t) (Ioi t) t)
      ∧ (∀ t, HasDerivWithinAt g (pressureLeftDeriv g t) (Iio t) t)
      ∧ (∀ t, Tendsto (slope g t) (𝓝[>] t) (𝓝 (pressureRightDeriv g t)))
      ∧ (∀ t, Tendsto (slope g t) (𝓝[<] t) (𝓝 (pressureLeftDeriv g t)))
      ∧ (∀ a b, Tendsto (fun n => slope (ivp2_tiltFreeEnergy (Gn n) 2) a b) atTop
          (𝓝 (slope g a b)))
      ∧ (∀ t, pressureLeftDeriv g t ≤ pressureRightDeriv g t)
      ∧ Monotone (pressureRightDeriv g)
      ∧ Monotone (pressureLeftDeriv g)
      ∧ {t : ℝ | pressureLeftDeriv g t ≠ pressureRightDeriv g t}.Countable :=
  cdl_convexDerivLimit (fun n => ivp2_tiltFreeEnergy (Gn n) 2) g hconv hlim


variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


theorem fpd_tiltFreeEnergy_deriv_eq_avgDensity (hE : 0 < G.edgeFinset.card) (t : ℝ) :
    HasDerivAt (ivp2_tiltFreeEnergy G 2)
      ((1 / (G.edgeFinset.card : ℝ)) * fkExpect G (fsc_logistic t) 2
        (fun ω => (openCount G ω : ℝ))) t := by
  have hbase := ivp2_tiltFreeEnergy_hasDerivAt G 2 (by norm_num) hE t
  rwa [← ivp2_cgfMean_eq_openCount_expect G 2 (by norm_num) t] at hbase


end FK
end StatMech
