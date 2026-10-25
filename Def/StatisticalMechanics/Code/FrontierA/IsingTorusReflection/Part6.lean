/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusGaussianDomination.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusReflection.Part6
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising

variable {d k : Nat}

def isingTorusHalvesEquiv (i : Fin d) :
    (ConfigSpace (IsingTorusLowerSite (k := k) i) ×
      ConfigSpace (IsingTorusLowerSite (k := k) i)) ≃
        ConfigSpace (IsingDyadicTorus d k) where
  toFun p := isingTorusGlueHalves i p.1 p.2
  invFun := isingTorusSplitHalves i
  left_inv p := by rcases p with ⟨lower, upper⟩; simp
  right_inv sigma := isingTorusGlueHalves_splitHalves i sigma


def isingTorusEmbedLower (i : Fin d)
    (u : IsingTorusLowerSite (k := k) i → Real) :
    IsingDyadicTorus d k → Real :=
  fun x => if hx : isingTorusInLowerHalf i x then u ⟨x, hx⟩ else 0

def isingTorusEmbedUpper (i : Fin d)
    (u : IsingTorusLowerSite (k := k) i → Real) :
    IsingDyadicTorus d k → Real :=
  fun x => if hx : isingTorusInLowerHalf i x then 0
    else u ⟨isingTorusReflectSite i x,
      (isingTorusReflectSite_not_lower_iff i x).mpr hx⟩

def isingTorusLowerValues (i : Fin d)
    (h : IsingDyadicTorus d k → Real)
    (sigma : ConfigSpace (IsingTorusLowerSite (k := k) i)) :
    IsingTorusLowerSite (k := k) i → Real :=
  fun x => spin sigma x + h x.1

def isingTorusUpperValues (i : Fin d)
    (h : IsingDyadicTorus d k → Real)
    (sigma : ConfigSpace (IsingTorusLowerSite (k := k) i)) :
    IsingTorusLowerSite (k := k) i → Real :=
  fun x => spin sigma x + h (isingTorusReflectSite i x.1)

end StatMech.FrontierA
