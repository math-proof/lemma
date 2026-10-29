/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWQOneMixedSquare.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.RSWStripSymmetry.Part5
import Theorem.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part101
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Theorem.StatisticalMechanics.Code.FK.IvProperties
import Theorem.StatisticalMechanics.Code.Percolation.PcUpperViaFK.Part4
import Theorem.StatisticalMechanics.Code.Percolation.OffClusterIndep.Part4
import Theorem.StatisticalMechanics.Code.Probability.InhomogeneousProduct.Part2
open Set SimpleGraph MeasureTheory
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Lattice

open StatMech.FK

open StatMech.RSW.Box

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem rq1_halfBernoulliMeasure_eq {E : Type*} [Countable E] :
    bernoulliProductMeasure (E := E)
        (⟨(1 : ℝ) / 2, by norm_num⟩ : NNReal)
          (by
            change (1 : ℝ) / 2 ≤ 1
            norm_num) =
      bernoulliProductMeasure (E := E) (2⁻¹ : NNReal) half_le_one := by
  have hp : (⟨(1 : ℝ) / 2, by norm_num⟩ : NNReal) = (2⁻¹ : NNReal) := by
    ext
    norm_num
  unfold bernoulliProductMeasure
  congr 1
  funext e
  exact bernoulliMeasure_congr _ _ hp

omit [DecidableEq V] in

theorem rq1_bcWeight_one (C : SimpleGraph V) [DecidableRel C.Adj]
    (p : ℝ) (omega : ConfigSpace (Sym2 V)) :
    bcWeight G C p 1 omega = edgeProduct G p omega := by
  simp [bcWeight]


theorem rq1_bcProb_one_eq_fkProb (C : SimpleGraph V) [DecidableRel C.Adj]
    (p : ℝ) (omega : ConfigSpace (Sym2 V)) :
    bcProb G C p 1 omega = fkProb G p 1 omega := by
  simp [bcProb, bcZ, bcWeight, fkProb, fkZ, fkWeight]


theorem rq1_bcEventMass_one_eq_bernoulli
    (C : SimpleGraph V) [DecidableRel C.Adj]
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (A : Set (ConfigSpace (Sym2 V)))
    (hA : _root_.DependsOn (A.indicator (fun _ => (1 : ℝ)))
      (G.edgeFinset : Set (Sym2 V))) :
    ∑ omega : ConfigSpace (Sym2 V),
        A.indicator (fun _ => (1 : ℝ)) omega * bcProb G C p 1 omega =
      (bernoulliProductMeasure (E := Sym2 V) ⟨p, hp.le⟩
        (by exact_mod_cast hp1.le)).real A := by
  simp_rw [rq1_bcProb_one_eq_fkProb G C p]
  exact fkProbOne_event_eq_bernoulli G hp hp1 A hA


end Universality
end StatMech
