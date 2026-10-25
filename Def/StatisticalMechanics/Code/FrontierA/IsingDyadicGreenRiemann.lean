/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDyadicGreenRiemann.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingDyadicGreenLowMomentum
import Theorem.StatisticalMechanics.Code.FrontierA.IsingInfraredSpatial
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Mathlib.Analysis.BoxIntegral.UnitPartition
import Mathlib.MeasureTheory.Order.UpperLower
import Abbrev.StatisticalMechanics.Code.FrontierA.IsingDyadicGreenRiemann
open Bornology Filter Finset MeasureTheory Set
open scoped BigOperators ComplexConjugate Pointwise Topology


namespace StatMech.FrontierA

variable {d : Nat}

open Lattice

def isingNormalizedCoordinateCube (d : Nat) :
    Set (IsingMomentumCoordinates d) :=
  {q | ∀ i, (-1 / 2 : Real) < q i ∧ q i ≤ 1 / 2}


def isingUnitMomentumLattice (d : Nat) :
    Submodule Int (IsingMomentumCoordinates d) :=
  Submodule.span Int (Set.range (Pi.basisFun Real (Fin d)))

noncomputable def isingNormalizedCoordinateDispersion
    (q : IsingMomentumCoordinates d) : Real :=
  ∑ i : Fin d, (2 - 2 * Real.cos (2 * Real.pi * q i))


noncomputable def isingRegularizedInverseDispersion
    (eta : Real) (q : IsingMomentumCoordinates d) : Real :=
  (max (isingNormalizedCoordinateDispersion q) eta)⁻¹


noncomputable def isingRegularizedGreenIntegrand
    (eta : Real) (x : Fin d → Int) (q : IsingMomentumCoordinates d) : Real :=
  Real.cos (2 * Real.pi * ∑ i : Fin d, q i * (x i : Real)) *
    isingRegularizedInverseDispersion eta q


noncomputable def isingRegularizedGridGreen
    (eta : Real) (x : Fin d → Int) (n : Nat) : Real :=
  (∑' q : ↑(isingNormalizedCoordinateCube d ∩
      (n : Real)⁻¹ • isingUnitMomentumLattice d),
      isingRegularizedGreenIntegrand eta x q) / n ^ d


noncomputable def isingRegularizedContinuumGreen
    (eta : Real) (x : Fin d → Int) : Real :=
  ∫ q in isingNormalizedCoordinateCube d,
    isingRegularizedGreenIntegrand eta x q

end StatMech.FrontierA
