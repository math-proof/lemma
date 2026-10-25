/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionFiniteVolume.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.PressureBCIndep
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionFiniteVolume
open scoped BigOperators
open Finset


namespace StatMech.Ising

open StatMech.Lattice

variable {d : ℕ}


noncomputable def finiteInterfaceFreeEnergy
    (i : Fin d) (n : ℕ) (beta : ℝ) : ℝ :=
  Real.log (fvZ (plusField d) n (bondFinsetTouch d n) beta 0) -
    Real.log (fvZ (interfaceField i) n (bondFinsetTouch d n) beta 0)


noncomputable def fvMeanNegEnergy
    (eta : ConfigSpace (Site d)) (n : ℕ)
    (B : Finset (Sym2 (Site d))) (beta h : ℝ) : ℝ :=
  (∑ tau : {x // x ∈ box d n} → Bool,
      fvWeight eta n B beta h tau * (-fvEnergy eta n B h tau)) /
    fvZ eta n B beta h


end StatMech.Ising
