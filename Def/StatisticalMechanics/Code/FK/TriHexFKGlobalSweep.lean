/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKGlobalSweep.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKExternalWeight
open Finset
open scoped BigOperators


namespace StatMech.FK.PeriodicPlanar

open Universality


def triangleFKLocalConnectivity : LocalConfig → ThreeTerminalConnectivity
  | (false, false, false) => .separate
  | (true, false, false) => .pair12
  | (false, true, false) => .pair20
  | (false, false, true) => .pair01
  | _ => .together


def starFKLocalConnectivity : LocalConfig → ThreeTerminalConnectivity
  | (false, false, false) => .separate
  | (true, false, false) => .separate
  | (false, true, false) => .separate
  | (false, false, true) => .separate
  | (true, true, false) => .pair01
  | (false, true, true) => .pair12
  | (true, false, true) => .pair20
  | (true, true, true) => .together


def triangleFKLocalOddsWeight (y0 y1 y2 : Real) : LocalConfig → Real
  | (b0, b1, b2) =>
      (if b0 then y0 else 1) * (if b1 then y1 else 1) *
        (if b2 then y2 else 1)


def starFKLocalOddsWeight (q y0 y1 y2 : Real) : LocalConfig → Real
  | (false, false, false) => q
  | (b0, b1, b2) =>
      (if b0 then y0 else 1) * (if b1 then y1 else 1) *
        (if b2 then y2 else 1)


end StatMech.FK.PeriodicPlanar
