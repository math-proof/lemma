/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DlrInfiniteSandwich.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.DlrSandwich
import Theorem.StatisticalMechanics.Code.FK.FKGeneralQConsumer.Part5
import Theorem.StatisticalMechanics.Code.FK.IvProperties
open MeasureTheory Filter Set
open scoped BigOperators


namespace StatMech

namespace FK

open StatMech.Lattice


noncomputable def dlrBcEventMass {V : Type*} [Fintype V] [DecidableEq V]
    (G C : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel C.Adj]
    (p q : ℝ) (A : Set (ConfigSpace (Sym2 V))) : ℝ :=
  ∑ omega, A.indicator (fun _ => (1 : ℝ)) omega * bcProb G C p q omega


noncomputable def IsFKDLR (d : ℕ) (p q : ℝ)
    (phi : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) : Prop := by
  classical
  exact ∀ n, ∃ weight : SimpleGraph (boxVerts d n) → ℝ,
      (∀ C, 0 ≤ weight C) ∧
      (∑ C, weight C = 1) ∧
      (∀ C, weight C ≠ 0 → C ≤ StatMech.Lattice.boundaryCliqueGraph (boxBoundary d n)) ∧
      ∀ A : Set (ConfigSpace (Sym2 (boxVerts d n))),
        (phi : Measure _).real (boxRestrict d n ⁻¹' A) =
          ∑ C, weight C * dlrBcEventMass (boxGraph d n) C p q A


end FK
end StatMech
