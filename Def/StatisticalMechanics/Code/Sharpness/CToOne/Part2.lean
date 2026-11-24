module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Sharpness.GHSFull.Part3
public import Theorem.StatisticalMechanics.Code.Sharpness.Simon.Part3
public import Theorem.StatisticalMechanics.Code.Sharpness.CToOne.Part2
open scoped BigOperators
open Filter Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CToOne.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Sharpness

open Ising

open Lattice


variable {V : Type*} [Fintype V] [DecidableEq V]


variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def sct_cInfDep (ι : ℕ → Type*) [∀ n, DecidableEq (ι n)]
    (M : ℕ → ℝ) (sites : (n : ℕ) → Finset (ι n))
    (m : (n : ℕ) → ι n → ℝ) (hne : ∀ n, (sites n).Nonempty) (n : ℕ) : ℝ :=
  (sites n).inf' (hne n) (fun y => M n / m n y)


end Sharpness
end StatMech
