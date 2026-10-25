/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CToOneLattice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.CToOne.Part3
import Theorem.StatisticalMechanics.Code.Ising.FiniteVolumeDomain
import Theorem.StatisticalMechanics.Code.Sharpness.CToOneLattice.Part2
open Filter Topology


namespace StatMech

namespace Sharpness

open Ising Lattice


noncomputable def sctBoxMag (d : ℕ) (β h : ℝ) (n : ℕ) (x : sctBox d n) : ℝ :=
  isingExpectation (sctBoxGraph d n) β h (fun s => spin s x)


noncomputable def sctOriginMag (d : ℕ) (β h : ℝ) (n : ℕ) : ℝ :=
  sctBoxMag d β h n (sctBoxOrigin d n)


noncomputable def sctBoxSites (d n : ℕ) : Finset (sctBox d n) := Finset.univ

end Sharpness
end StatMech
