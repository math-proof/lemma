/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonTrifurcation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.bfin2assemble
import Theorem.StatisticalMechanics.Code.Percolation.CanonicalTrifCount.Part4
import Theorem.StatisticalMechanics.Code.Percolation.OutwardArmForestClose.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonTrifurcation


namespace StatMech.FrontierA

open Finset SimpleGraph Set

open StatMech.Lattice StatMech.ConfigSpace

open StatMech.Percolation

open StatMech.Walls


variable {V : Type*} [Fintype V] [Nonempty V]


variable {d : ℕ}


noncomputable def canonicalTrifurcationsInBox
    (omega : ConfigSpace (Sym2 (Site d))) (R : ℕ) : Finset (Site d) := by
  classical
  exact (box_finite d (R - 1)).toFinset.filter fun x =>
    IsCanonicalTrifurcation d omega x

end StatMech.FrontierA
