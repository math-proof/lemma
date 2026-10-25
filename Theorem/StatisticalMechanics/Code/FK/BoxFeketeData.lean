/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxFeketeData.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.UniformBulkDeviation.Part2
import Theorem.StatisticalMechanics.Code.FK.FKPressureDeriv.Part4
open MeasureTheory Set Filter Topology Real
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.openClassical false
set_option linter.style.setOption false


namespace StatMech

namespace FK

open ConfigSpace StatMech.Lattice


theorem bfd_tendsto_div_of_nearSubadditive (u c : ℕ → ℝ)
    (hsub : Subadditive (fun n => u n + c n))
    (hbdd : BddBelow (Set.range fun n => (u n + c n) / n))
    (hc : Tendsto (fun n => c n / n) atTop (𝓝 0)) :
    Tendsto (fun n => u n / n) atTop (𝓝 hsub.lim) := by
  have hw : Tendsto (fun n => (u n + c n) / n) atTop (𝓝 hsub.lim) := hsub.tendsto_lim hbdd
  have hsplit : (fun n => u n / n) = fun n => (u n + c n) / n - c n / n := by
    funext n; rw [add_div]; ring
  rw [hsplit]
  simpa using hw.sub hc


theorem bfd_tendsto_perEdge_of_nearSubadditive (u c : ℕ → ℝ)
    (hsub : Subadditive (fun n => u n + c n))
    (hbdd : BddBelow (Set.range fun n => (u n + c n) / n))
    (hc : Tendsto (fun n => c n / n) atTop (𝓝 0))
    (e : ℕ → ℝ) (κ : ℝ) (hκ : κ ≠ 0)
    (he : Tendsto (fun n => e n / n) atTop (𝓝 κ)) :
    Tendsto (fun n => u n / e n) atTop (𝓝 (hsub.lim / κ)) := by
  have hun : Tendsto (fun n => u n / n) atTop (𝓝 hsub.lim) :=
    bfd_tendsto_div_of_nearSubadditive u c hsub hbdd hc
  have hdiv : Tendsto (fun n => (u n / n) / (e n / n)) atTop (𝓝 (hsub.lim / κ)) := hun.div he hκ
  refine hdiv.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hnpos : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  field_simp


variable {V : ℕ → Type*} [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
  (Gn : ∀ n, SimpleGraph (V n)) [∀ n, DecidableRel (Gn n).Adj]


theorem bfd_tiltFreeEnergy_tendsto_of_nearSubadditive (q : ℝ) (hq : 0 < q) (t : ℝ)
    (hE : ∀ n, 0 < (Gn n).edgeFinset.card)
    (c : ℕ → ℝ)
    (hsub : Subadditive (fun n => - Real.log (fkZ (Gn n) (fsc_logistic t) q) + c n))
    (hbdd : BddBelow (Set.range fun n =>
      (- Real.log (fkZ (Gn n) (fsc_logistic t) q) + c n) / n))
    (hc : Tendsto (fun n => c n / n) atTop (𝓝 0))
    (κ : ℝ) (hκ : κ ≠ 0)
    (he : Tendsto (fun n => ((Gn n).edgeFinset.card : ℝ) / n) atTop (𝓝 κ)) :
    Tendsto (fun n => ivp2_tiltFreeEnergy (Gn n) q t) atTop
      (𝓝 (- (hsub.lim / κ) + Real.log (1 + Real.exp t))) := by
  set u : ℕ → ℝ := fun n => - Real.log (fkZ (Gn n) (fsc_logistic t) q) with hu
  set e : ℕ → ℝ := fun n => ((Gn n).edgeFinset.card : ℝ) with hedef
  
  have hratio : Tendsto (fun n => u n / e n) atTop (𝓝 (hsub.lim / κ)) :=
    bfd_tendsto_perEdge_of_nearSubadditive u c hsub hbdd hc e κ hκ he
  
  have hform : (fun n => ivp2_tiltFreeEnergy (Gn n) q t)
      = fun n => - (u n / e n) + Real.log (1 + Real.exp t) := by
    funext n
    unfold ivp2_tiltFreeEnergy
    have hp0 : (0:ℝ) < fsc_logistic t := fsc_logistic_pos t
    have hp1 : fsc_logistic t < 1 := fsc_logistic_lt_one t
    have hZ : 0 < fkZ (Gn n) (fsc_logistic t) q := fkZ_pos (Gn n) hp0 hp1 hq
    have hEne : ((Gn n).edgeFinset.card : ℝ) ≠ 0 := by exact_mod_cast (hE n).ne'
    simp only [hu, hedef]
    field_simp
  rw [hform]
  have hneg : Tendsto (fun n => - (u n / e n)) atTop (𝓝 (- (hsub.lim / κ))) := hratio.neg
  simpa using hneg.add_const (Real.log (1 + Real.exp t))


end FK
end StatMech
