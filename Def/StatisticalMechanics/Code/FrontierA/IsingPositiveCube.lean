/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingPositiveCube.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusBlockQuantitative
import Theorem.StatisticalMechanics.Code.FrontierA.IsingMessagerMiracleInfinite
open Finset Set
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech Lattice

variable {d m k : Nat}


def isingPositiveCubeEmbedding (d m : Nat) :
    (Fin d -> Fin m) ↪ Site d where
  toFun a i := (a i : Nat)
  inj' := by
    intro a b h
    funext i
    apply Fin.ext
    have hi := congrFun h i
    change (((a i).val : Nat) : Int) = ((b i).val : Int) at hi
    exact_mod_cast hi


def isingPositiveCube (d m : Nat) : Finset (Site d) :=
  Finset.univ.map (isingPositiveCubeEmbedding d m)

end StatMech.FrontierA
