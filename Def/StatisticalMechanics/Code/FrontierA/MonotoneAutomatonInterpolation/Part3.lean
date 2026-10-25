/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonInterpolation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonLaw.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonInterpolation.Part2
open MeasureTheory


namespace StatMech.FrontierA

open StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

variable {d : ℕ}


noncomputable def interpolatedSiteLaw (T : MonotoneAutomaton d)
    (mu : Measure (FieldTriple d)) : Measure (ConfigSpace (Site d)) :=
  Measure.map (interpolatedSite T) mu


noncomputable def interpolatedBondLaw (T : MonotoneAutomaton d)
    (mu : Measure (FieldTriple d)) :
    Measure (ConfigSpace (Sym2 (Site d))) :=
  Measure.map (siteToBond ∘ interpolatedSite T) mu

end StatMech.FrontierA
