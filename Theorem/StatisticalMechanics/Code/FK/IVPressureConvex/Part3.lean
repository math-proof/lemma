/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IVPressureConvex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.Tilt.Part3
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.FK.SecantClose.Part3
import Def.StatisticalMechanics.Code.FK.IVPressureConvex.Part2
open MeasureTheory Set Filter Topology Real Finset
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace FK

open ConfigSpace StatMech.Lattice


variable {ι : Type*} [Fintype ι]


theorem ivp2_Kcgf_hasDerivAt (w a : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hpos : ∃ i, 0 < w i) (t : ℝ) :
    HasDerivAt (ivp2_Kcgf w a) (ivp2_S1 w a t / ivp2_Ssum w a t) t := by
  have hS := ivp2_Ssum_hasDerivAt w a t
  have := hS.log (ivp2_Ssum_pos w a hw hpos t).ne'
  convert this using 1

theorem ivp2_deriv_Kcgf (w a : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hpos : ∃ i, 0 < w i) :
    deriv (ivp2_Kcgf w a) = fun t => ivp2_S1 w a t / ivp2_Ssum w a t := by
  funext t; exact (ivp2_Kcgf_hasDerivAt w a hw hpos t).deriv


theorem ivp2_Kcgf_deriv2_hasDerivAt (w a : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hpos : ∃ i, 0 < w i)
    (t : ℝ) :
    HasDerivAt (fun s => ivp2_S1 w a s / ivp2_Ssum w a s)
      ((ivp2_S2 w a t * ivp2_Ssum w a t - ivp2_S1 w a t * ivp2_S1 w a t)
        / (ivp2_Ssum w a t) ^ 2) t := by
  have h1 := ivp2_S1_hasDerivAt w a t
  have h2 := ivp2_Ssum_hasDerivAt w a t
  have hne := (ivp2_Ssum_pos w a hw hpos t).ne'
  have := h1.div h2 hne
  convert this using 1


theorem ivp2_Kcgf_deriv2_nonneg (w a : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hpos : ∃ i, 0 < w i)
    (t : ℝ) : 0 ≤ (deriv^[2] (ivp2_Kcgf w a)) t := by
  show 0 ≤ deriv (deriv (ivp2_Kcgf w a)) t
  rw [ivp2_deriv_Kcgf w a hw hpos, (ivp2_Kcgf_deriv2_hasDerivAt w a hw hpos t).deriv]
  apply div_nonneg
  · have hcs := ivp2_cauchy_schwarz_cgf w a hw t
    nlinarith [hcs]
  · positivity


theorem ivp2_Kcgf_convexOn (w a : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hpos : ∃ i, 0 < w i) :
    ConvexOn ℝ univ (ivp2_Kcgf w a) := by
  apply convexOn_univ_of_deriv2_nonneg
  · exact fun t => (ivp2_Kcgf_hasDerivAt w a hw hpos t).differentiableAt
  · rw [ivp2_deriv_Kcgf w a hw hpos]
    exact fun t => (ivp2_Kcgf_deriv2_hasDerivAt w a hw hpos t).differentiableAt
  · exact ivp2_Kcgf_deriv2_nonneg w a hw hpos


variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableEq V] in


theorem ivp2_edgeProduct_logistic (t : ℝ) (ω : ConfigSpace (Sym2 V)) :
    edgeProduct G (fsc_logistic t) ω
      = Real.exp (openCount G ω * t) / (1 + Real.exp t) ^ G.edgeFinset.card := by
  rw [edgeProduct_eq_pow]
  unfold fsc_logistic
  have hpos : (0:ℝ) < 1 + Real.exp t := by positivity
  have h1 : (1 : ℝ) - Real.exp t / (1 + Real.exp t) = 1 / (1 + Real.exp t) := by
    field_simp; ring
  have hexp : Real.exp (openCount G ω * t) = (Real.exp t) ^ (openCount G ω) := by
    rw [← Real.exp_nat_mul]
  rw [h1, div_pow, div_pow, one_pow, ← openCount_add_closedCount G ω, pow_add, hexp]
  field_simp


theorem ivp2_fkWeight_logistic (t q : ℝ) (ω : ConfigSpace (Sym2 V)) :
    fkWeight G (fsc_logistic t) q ω
      = (q ^ numClusters G ω * Real.exp ((openCount G ω : ℝ) * t))
          / (1 + Real.exp t) ^ G.edgeFinset.card := by
  unfold fkWeight
  rw [ivp2_edgeProduct_logistic G t ω]
  ring


theorem ivp2_fkZ_logistic (t q : ℝ) :
    fkZ G (fsc_logistic t) q
      = ivp2_Ssum (fun ω => q ^ numClusters G ω) (fun ω => (openCount G ω : ℝ)) t
          / (1 + Real.exp t) ^ G.edgeFinset.card := by
  unfold fkZ ivp2_Ssum
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ω _
  rw [ivp2_fkWeight_logistic G t q ω]


end FK
end StatMech
