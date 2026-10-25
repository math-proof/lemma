/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/MonotonicOSSS.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.Coding.Part6
import Theorem.StatisticalMechanics.Code.OSSS.CovLowerBound
import Theorem.StatisticalMechanics.Code.FK.FKG
import Theorem.StatisticalMechanics.Code.FK.RussoDerivative.Part5
import Def.StatisticalMechanics.Code.OSSS.MonotonicOSSS.Part2
open scoped BigOperators
open Finset MeasureTheory Set

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace OSSS

namespace MonotonicFK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

open MonotonicMeasure


lemma genMean_fkMass (p q : ℝ) (g : ConfigSpace (Sym2 V) → ℝ) :
    genMean (fkMass G p q) g = FK.fkMean G p q g := by
  unfold genMean fkMass FK.fkMean
  rfl


lemma genCov_fkMass (p q : ℝ) (f g : ConfigSpace (Sym2 V) → ℝ) :
    genCov (fkMass G p q) f g = FK.fkCov G p q f g := by
  unfold genCov FK.fkCov
  rw [genMean_fkMass, genMean_fkMass, genMean_fkMass]


lemma genCoord_eq_coord (e : Sym2 V) : (genCoord e : ConfigSpace (Sym2 V) → ℝ) = FK.coord e := by
  funext ω; unfold genCoord FK.coord; rfl


lemma genVar_fkMass_indicator (p q : ℝ) (A : Set (ConfigSpace (Sym2 V))) :
    genVar (fkMass G p q) (A.indicator (fun _ => (1 : ℝ)))
      = FK.fkCov G p q (A.indicator (fun _ => (1 : ℝ))) (A.indicator (fun _ => (1 : ℝ))) := by
  unfold genVar
  rw [genCov_fkMass]


lemma fkVar_indicator (p q : ℝ)
    (A : Set (ConfigSpace (Sym2 V))) :
    genVar (fkMass G p q) (A.indicator (fun _ => (1 : ℝ)))
      = FK.fkProbOf G p q A * (1 - FK.fkProbOf G p q A) := by
  rw [genVar_fkMass_indicator]
  
  have hidem : (fun ω => A.indicator (fun _ => (1 : ℝ)) ω * A.indicator (fun _ => (1 : ℝ)) ω)
      = A.indicator (fun _ => (1 : ℝ)) := by
    classical
    funext ω
    rw [Set.indicator_apply]
    split_ifs <;> norm_num
  unfold FK.fkCov
  rw [hidem]
  
  show FK.fkMean G p q (A.indicator (fun _ => (1 : ℝ)))
      - FK.fkMean G p q (A.indicator (fun _ => (1 : ℝ)))
        * FK.fkMean G p q (A.indicator (fun _ => (1 : ℝ)))
    = FK.fkProbOf G p q A * (1 - FK.fkProbOf G p q A)
  unfold FK.fkProbOf
  ring

end MonotonicFK
end OSSS
end StatMech
