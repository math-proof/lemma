/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCorrections.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.GHSVertexPartition.Part8


namespace StatMech.FrontierA

open Finset

open scoped symmDiff

open StatMech.Ising

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]


def grahamPairSupport (x y : V) : Finset V := {x} ∆ {y}


def grahamFourSupport (i j k l : V) : Finset V :=
  grahamPairSupport i j ∆ grahamPairSupport k l


noncomputable def grahamTwoPoint (E : Finset (Sym2 V)) (J : Sym2 V → ℝ)
    (x y : V) : ℝ :=
  expJ E J (fun _ => 0) (spinProd (grahamPairSupport x y))


noncomputable def grahamFourPoint (E : Finset (Sym2 V)) (J : Sym2 V → ℝ)
    (i j k l : V) : ℝ :=
  expJ E J (fun _ => 0) (spinProd (grahamFourSupport i j k l))


noncomputable def grahamUrsell4 (E : Finset (Sym2 V)) (J : Sym2 V → ℝ)
    (i j k l : V) : ℝ :=
  grahamFourPoint E J i j k l
    - grahamTwoPoint E J i j * grahamTwoPoint E J k l
    - grahamTwoPoint E J i k * grahamTwoPoint E J j l
    - grahamTwoPoint E J i l * grahamTwoPoint E J j k

end StatMech.FrontierA
