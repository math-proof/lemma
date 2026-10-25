/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_covcorrelatedframe.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.MonotonicOSSS.Part3
import Theorem.StatisticalMechanics.Code.Walls.oc_core.Part3
import Def.StatisticalMechanics.Code.Walls.oc2_covcorrelatedframe
open scoped BigOperators
open Finset

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


namespace StatMech

namespace Walls

open StatMech.OSSS

open StatMech.OSSS.MonotonicMeasure

open StatMech.OSSS.MonotonicFK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


lemma oc2_meanCorr_eq (p q : ℝ) (g : ConfigSpace (Sym2 V) → ℝ) :
    oc2_meanCorr G p q g = ∑ ω, g ω * fkMass G p q ω := rfl


lemma oc2_covCorr_def (p q : ℝ) (f g : ConfigSpace (Sym2 V) → ℝ) :
    oc2_covCorr G p q f g
      = oc2_meanCorr G p q (fun ω => f ω * g ω)
        - oc2_meanCorr G p q f * oc2_meanCorr G p q g := rfl


lemma oc2_coordRead_apply (e : Sym2 V) (ω : ConfigSpace (Sym2 V)) :
    oc2_coordRead e ω = if ω e then (1 : ℝ) else 0 := rfl


lemma oc2_meanCorr_eq_fkMean (p q : ℝ) (g : ConfigSpace (Sym2 V) → ℝ) :
    oc2_meanCorr G p q g = FK.fkMean G p q g :=
  genMean_fkMass G p q g


lemma oc2_covCorr_eq_fkCov (p q : ℝ) (f g : ConfigSpace (Sym2 V) → ℝ) :
    oc2_covCorr G p q f g = FK.fkCov G p q f g :=
  genCov_fkMass G p q f g


lemma oc2_coordRead_eq_coord (e : Sym2 V) :
    oc2_coordRead e = (FK.coord e : ConfigSpace (Sym2 V) → ℝ) :=
  genCoord_eq_coord e


lemma oc2_covCorr_symm (p q : ℝ) (f g : ConfigSpace (Sym2 V) → ℝ) :
    oc2_covCorr G p q f g = oc2_covCorr G p q g f := by
  simp only [oc2_covCorr, genCov, genMean]
  rw [mul_comm (∑ ω, f ω * fkMass G p q ω)]
  congr 1
  exact Finset.sum_congr rfl (fun ω _ => by ring)


lemma oc2_covCorr_add_right (p q : ℝ) (f g h : ConfigSpace (Sym2 V) → ℝ) :
    oc2_covCorr G p q f (fun ω => g ω + h ω)
      = oc2_covCorr G p q f g + oc2_covCorr G p q f h := by
  rw [oc2_covCorr_eq_fkCov, oc2_covCorr_eq_fkCov, oc2_covCorr_eq_fkCov]
  exact FK.fkCov_add_right G p q f g h


lemma oc2_covCorr_sum_right (p q : ℝ) {ι : Type*} (s : Finset ι)
    (f : ConfigSpace (Sym2 V) → ℝ) (g : ι → ConfigSpace (Sym2 V) → ℝ) :
    oc2_covCorr G p q f (fun ω => ∑ i ∈ s, g i ω)
      = ∑ i ∈ s, oc2_covCorr G p q f (g i) := by
  rw [oc2_covCorr_eq_fkCov]
  rw [show (∑ i ∈ s, oc2_covCorr G p q f (g i))
      = ∑ i ∈ s, FK.fkCov G p q f (g i) from
    Finset.sum_congr rfl (fun i _ => oc2_covCorr_eq_fkCov G p q f (g i))]
  exact FK.fkCov_sum_right G p q s f g


lemma oc2_meanCorr_const_mul (p q : ℝ) (c : ℝ) (g : ConfigSpace (Sym2 V) → ℝ) :
    oc2_meanCorr G p q (fun ω => c * g ω) = c * oc2_meanCorr G p q g := by
  rw [oc2_meanCorr_eq_fkMean, oc2_meanCorr_eq_fkMean]
  exact FK.fkMean_const_mul G p q c g


lemma oc2_meanCorr_add (p q : ℝ) (g h : ConfigSpace (Sym2 V) → ℝ) :
    oc2_meanCorr G p q (fun ω => g ω + h ω)
      = oc2_meanCorr G p q g + oc2_meanCorr G p q h := by
  rw [oc2_meanCorr_eq_fkMean, oc2_meanCorr_eq_fkMean, oc2_meanCorr_eq_fkMean]
  exact FK.fkMean_add G p q g h


lemma oc2_covCorr_smul_right (p q : ℝ) (c : ℝ) (f g : ConfigSpace (Sym2 V) → ℝ) :
    oc2_covCorr G p q f (fun ω => c * g ω) = c * oc2_covCorr G p q f g := by
  rw [oc2_covCorr_def, oc2_covCorr_def,
      show (fun ω => f ω * (c * g ω)) = (fun ω => c * (f ω * g ω)) from by funext ω; ring,
      oc2_meanCorr_const_mul G p q c (fun ω => f ω * g ω),
      oc2_meanCorr_const_mul G p q c g]
  ring


lemma oc2_covCorr_const_right (p q : ℝ) (f : ConfigSpace (Sym2 V) → ℝ) {c : ℝ}
    (hZ : FK.fkZ G p q ≠ 0) :
    oc2_covCorr G p q f (fun _ => c) = 0 := by
  rw [oc2_covCorr_def]
  have hc : oc2_meanCorr G p q (fun _ => c) = c := by
    rw [oc2_meanCorr_eq_fkMean]; exact FK.fkMean_const G p q hZ
  have hfc : oc2_meanCorr G p q (fun ω => f ω * (fun _ => c) ω)
      = c * oc2_meanCorr G p q f := by
    rw [show (fun ω => f ω * (fun _ => c) ω) = (fun ω => c * f ω) from by funext ω; ring]
    exact oc2_meanCorr_const_mul G p q c f
  rw [hfc, hc]
  ring


lemma oc2_meanCorr_one (p q : ℝ) (hZ : FK.fkZ G p q ≠ 0) :
    oc2_meanCorr G p q (fun _ => (1 : ℝ)) = 1 := by
  rw [oc2_meanCorr_eq_fkMean]; exact FK.fkMean_const G p q hZ


end Walls
end StatMech
