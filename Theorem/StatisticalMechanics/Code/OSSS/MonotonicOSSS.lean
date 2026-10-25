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
import Def.StatisticalMechanics.Code.OSSS.MonotonicOSSS
open scoped BigOperators
open Finset MeasureTheory Set

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace OSSS

namespace MonotonicFK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


lemma fkMass_pos {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (ω : ConfigSpace (Sym2 V)) :
    0 < fkMass G p q ω := FK.fkProb_pos G hp hp1 hq ω


lemma fkMass_sum_eq_one {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ∑ ω : ConfigSpace (Sym2 V), fkMass G p q ω = 1 := FK.fkProb_sum_eq_one G hp hp1 hq


theorem fk_codeProb_eq_mass {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    {n : ℕ} (σ : Fin n ≃ Sym2 V) (x : ConfigSpace (Sym2 V)) :
    (∏ t : Fin n, Coding.condProbBit (fkMass G p q)
        (Coding.prefixSet (σ : Fin n → Sym2 V) (t : ℕ)) x
        ((σ : Fin n → Sym2 V) t) (x ((σ : Fin n → Sym2 V) t)))
      = fkMass G p q x :=
  Coding.codeProb_eq_mass (fkMass G p q) (fkMass_pos G hp hp1 hq)
    (fkMass_sum_eq_one G hp hp1 hq) σ x


theorem fk_volume_codeFibre {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    {n : ℕ} (σ : Fin n ≃ Sym2 V) (x : ConfigSpace (Sym2 V)) :
    (volume (Coding.codeFibre (fkMass G p q) σ x)).toReal = fkMass G p q x :=
  Coding.volume_codeFibre (fkMass G p q) (fkMass_pos G hp hp1 hq)
    (fkMass_sum_eq_one G hp hp1 hq) σ x


theorem fkMass_isMonotonic {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    Monotonic.IsMonotonicMeasure (fkMass G p q) := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  exact Monotonic.fkg_implies_monotonic
    (fun ω => fkMass_pos G hp hp1 hq0 ω)
    (FK.fkProb_FKGLatticeCondition G hp hp1 hq)

end MonotonicFK
end OSSS
end StatMech
