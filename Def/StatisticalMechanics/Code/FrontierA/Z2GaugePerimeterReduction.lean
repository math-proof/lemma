/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugePerimeterReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeThermodynamicReduction.Part2
import Theorem.StatisticalMechanics.Code.FK.TwoPoint.Part4
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
open scoped BigOperators


namespace StatMech.FrontierA

noncomputable section

def finiteEventMass {E : Type*} [Fintype E] [DecidableEq E]
    (pi : ConfigSpace E -> Real) (A : Set (ConfigSpace E)) : Real :=
  ∑ omega, pi omega * A.indicator (fun _ => (1 : Real)) omega

end
end StatMech.FrontierA
