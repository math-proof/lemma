/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeBoxEvenLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Sharpness.MeanfieldIsingState.Part2
import Theorem.StatisticalMechanics.Code.Ising.FiniteVolumeDomain
import Theorem.StatisticalMechanics.Code.Ising.IsingTranslatedBoxClose.Part3
import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
import Theorem.StatisticalMechanics.Code.FrontierB.FiniteCurrentParity.Part2
import Def.StatisticalMechanics.Code.FrontierB.FreeBoxEvenLimit.Part3
open MeasureTheory Filter Topology
open scoped BigOperators symmDiff


namespace StatMech.FrontierB

open StatMech.Ising StatMech.Lattice StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem prod_bond_eq_spinProd_edgeBoundary
    {V : Type*} [DecidableEq V]
    (F : Finset (Sym2 V)) (hF : ∀ e ∈ F, ¬ e.IsDiag)
    (s : ConfigSpace V) :
    (∏ e ∈ F, bond s e) = spinProd (edgeBoundary F) s := by
  classical
  induction F using Finset.induction with
  | empty => simp [edgeBoundary, spinProd]
  | @insert e F he ih =>
      have hediag : ¬ e.IsDiag := hF e (Finset.mem_insert_self e F)
      have hF' : ∀ f ∈ F, ¬ f.IsDiag := fun f hf => hF f (Finset.mem_insert_of_mem hf)
      have hebond : bond s e = spinProd e.toFinset s := by
        induction e using Sym2.inductionOn with
        | _ x y =>
            have hxy : x ≠ y := by simpa [Sym2.IsDiag] using hediag
            rw [bond_mk, Sym2.toFinset_mk_eq, spinProd, Finset.prod_pair hxy]
      rw [Finset.prod_insert he, edgeBoundary, Finset.fold_insert he,
        hebond, ih hF', ← spinProd_mul_self]
      rfl

end StatMech.FrontierB
