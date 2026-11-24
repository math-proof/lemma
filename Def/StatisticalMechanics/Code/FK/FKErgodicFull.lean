module
public import Theorem.StatisticalMechanics.Code.Foundations.WeakConvergence
public import Theorem.StatisticalMechanics.Code.Foundations.Ergodicity.Part2
public import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
public import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
public import Theorem.StatisticalMechanics.Code.FK.FKErgodicFull
open MeasureTheory Filter Topology
open StatMech.ConfigSpace StatMech.Lattice


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKErgodicFull.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace FK

variable {d : ℕ}


noncomputable def erg_wiredShiftedFinite {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (g : Multiplicative (Site d)) (n : ℕ) :
    ProbabilityMeasure (ConfigSpace (Sym2 (Site d))) :=
  (wiredFiniteMeasure d n hp hp1 hq).map (continuous_shift g).measurable.aemeasurable


noncomputable def erg_freeShiftedFinite {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (g : Multiplicative (Site d)) (n : ℕ) :
    ProbabilityMeasure (ConfigSpace (Sym2 (Site d))) :=
  (freeFiniteMeasure d n hp hp1 hq).map (continuous_shift g).measurable.aemeasurable


end FK
end StatMech
