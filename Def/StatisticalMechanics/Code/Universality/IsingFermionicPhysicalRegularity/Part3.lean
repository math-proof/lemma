module
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalEnergy
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialPatch.Part15
public import Mathlib.Data.Nat.Choose.Vandermonde
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRegularity.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRegularity.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

open Finset


noncomputable def isingBinomialWeight (n k : Nat) : Real :=
  (n.choose k : Real) / 2 ^ n


noncomputable def isingBinomialWeightPrev (n k : Nat) : Real :=
  if k = 0 then 0 else isingBinomialWeight n (k - 1)

end
end StatMech.Universality
