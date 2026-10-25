/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingFreeStateCoordinateSymmetry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingDiagonalReflectionInfinite.Part2
open Filter MeasureTheory Set Topology


namespace StatMech.FrontierA

open StatMech Ising Lattice StatMech.FrontierB

variable {d : Nat}

noncomputable def freeBoxAutomorphismEquiv
    (e : Site d ≃ Site d)
    (hbox : ∀ n x, x ∈ boxFinset d n ↔ e x ∈ boxFinset d n)
    (n : Nat) :
    freeDomainVertices (boxFinset d n) ≃
      freeDomainVertices (boxFinset d n) where
  toFun x := ⟨e x.1, (hbox n x.1).1 x.2⟩
  invFun x := ⟨e.symm x.1, by
    apply (hbox n (e.symm x.1)).2
    simpa using x.2⟩
  left_inv x := by ext; simp
  right_inv x := by ext; simp

end StatMech.FrontierA
