/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexCounterexample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneP3Domain
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneSupportLexCounterexample
open Finset


namespace StatMech.Sharpness

def shbK4DirectFiberMass (E : Finset shbK4Edge) (t : ℚ) : ℚ :=
  ∑ A ∈ shbK4Configs E, if shbK4SelectsDirect03 A then t ^ A.card else 0


def shbK4VacuumMass (E : Finset shbK4Edge) (t : ℚ) : ℚ :=
  ∑ A ∈ shbK4Configs E, if shbK4Boundary A = ∅ then t ^ A.card else 0


def shbK4DirectRho (E : Finset shbK4Edge) (t : ℚ) : ℚ :=
  shbK4DirectFiberMass E t / shbK4VacuumMass E t


end StatMech.Sharpness
