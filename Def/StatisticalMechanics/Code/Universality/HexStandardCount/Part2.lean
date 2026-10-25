/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStandardCount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralConnEndgame
import Theorem.StatisticalMechanics.Code.Universality.HexInfraHeading
import Theorem.StatisticalMechanics.Code.Universality.HexStandardCount


namespace StatMech.Universality

open Filter HexWalk Topology

open scoped Real Topology

noncomputable section

noncomputable def hexRootedOrientationFinset (h : ℤ) (n : ℕ) :
    Finset (List ℂ) :=
  (hlc_sawFinset (-halfStep h) h n).image (hexRootedVertices h)


noncomputable def hexStandardSAWFinset (n : ℕ) : Finset (List ℂ) :=
  hexRootedOrientationFinset 0 n ∪
    (hexRootedOrientationFinset 2 n ∪ hexRootedOrientationFinset 4 n)


noncomputable def hexStandardSAWCountNat (n : ℕ) : ℕ :=
  (hexStandardSAWFinset n).card


noncomputable def hexStandardSAWCount (n : ℕ) : ℝ :=
  (hexStandardSAWCountNat n : ℝ)

end
end StatMech.Universality
