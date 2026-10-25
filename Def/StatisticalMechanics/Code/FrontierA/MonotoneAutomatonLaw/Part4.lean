/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonSiteBond.Part2
import Instance.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonLaw
open MeasureTheory
open scoped NNReal


namespace StatMech.FrontierA

open StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

variable {d : ℕ}


noncomputable def automatonSiteLaw (T : MonotoneAutomaton d)
    (mu : Measure (NonnegativeField d)) : Measure (ConfigSpace (Site d)) :=
  Measure.map T mu


noncomputable def automatonBondLaw (T : MonotoneAutomaton d)
    (mu : Measure (NonnegativeField d)) :
    Measure (ConfigSpace (Sym2 (Site d))) :=
  Measure.map (siteToBond ∘ T) mu


end StatMech.FrontierA
