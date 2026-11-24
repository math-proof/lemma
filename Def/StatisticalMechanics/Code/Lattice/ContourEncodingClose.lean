module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.ClusterContourBijection.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.CanonicalContour.Part6
public import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
open Set Finset SimpleGraph
open StatMech.Ising


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourEncodingClose.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Lattice

attribute [local instance] Classical.propDecidable

variable {d : ℕ}


noncomputable def indicatorConfig (K : Finset (Site d)) : ConfigSpace (Sym2 (Site d)) :=
  fun e => Sym2.lift ⟨fun x y => decide (x ∈ K ∧ y ∈ K), by
    intro x y; simp only [decide_eq_decide]; tauto⟩ e

end Lattice
end StatMech
