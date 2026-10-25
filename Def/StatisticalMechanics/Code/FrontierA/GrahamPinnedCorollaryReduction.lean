/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedCorollaryReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamPinnedFieldAdapter.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamMarkedSiteCorollary
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamPinnedCorollaryReduction
open Finset
open scoped BigOperators
open Classical


namespace StatMech.FrontierA

open StatMech.ConfigSpace StatMech.Ising StatMech.Sharpness

open StatMech.Walls.VBG

variable {V : Type*} [Fintype V] [DecidableEq V]


noncomputable def grahamFieldFourPointLHS
    (E : Finset (Sym2 V)) (K : Sym2 V -> Real) (h : V -> Real)
    (i j k l : V) : Real :=
  expJ E K h (fun t => (spin t i * spin t j) * (spin t k * spin t l)) -
    expJ E K h (fun t => spin t i * spin t j) *
      expJ E K h (fun t => spin t k * spin t l) -
    expJ E K h (fun t => spin t i * spin t k) *
      expJ E K h (fun t => spin t j * spin t l) -
    expJ E K h (fun t => spin t i * spin t l) *
      expJ E K h (fun t => spin t j * spin t k)


noncomputable def grahamFieldCovariance
    (E : Finset (Sym2 V)) (K : Sym2 V -> Real) (h : V -> Real)
    (x y : V) : Real :=
  expJ E K h (fun t => spin t x * spin t y) -
    expJ E K h (fun t => spin t x) *
      expJ E K h (fun t => spin t y)


noncomputable def grahamFieldFourPointRHS
    (E : Finset (Sym2 V)) (K : Sym2 V -> Real) (h : V -> Real)
    (i j k l : V) : Real :=
  -2 * expJ E K h (fun t => spin t i) *
      expJ E K h (fun t => spin t j) *
      expJ E K h (fun t => spin t k) *
      expJ E K h (fun t => spin t l) -
    2 * grahamFieldCovariance E K h i k *
      grahamFieldCovariance E K h j k *
      expJ E K h (fun t => spin t k * spin t l) -
    2 * expJ E K h (fun t => spin t i) *
      expJ E K h (fun t => spin t j) *
      grahamFieldCovariance E K h i k *
      grahamFieldCovariance E K h i l


end StatMech.FrontierA
