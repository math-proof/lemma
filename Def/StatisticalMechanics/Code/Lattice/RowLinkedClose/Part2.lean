module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
public import Theorem.StatisticalMechanics.Code.Lattice.OrbitExteriorEven
public import Theorem.StatisticalMechanics.Code.Lattice.JordanInteriorLib.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.RowLinkedClose.Part2
open Set SimpleGraph Function


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RowLinkedClose.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Lattice

def rlc_DownLink {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) (seed : Site 2) (M : ℤ) :
    Prop :=
  ∀ z ∈ jil_offSupportInterior Vc, z ≠ seed →
    ∃ z' ∈ jil_offSupportInterior Vc,
      rlc_lexMeasure M z' < rlc_lexMeasure M z ∧
      ∃ p : (hypercubicLattice 2).Walk z z', ∀ w ∈ p.support, w ∉ Vc.support


end Lattice
end StatMech
