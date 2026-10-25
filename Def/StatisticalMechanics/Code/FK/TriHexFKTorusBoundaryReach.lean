/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKTorusBoundaryReach.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKTorusHomogeneous


namespace StatMech.FK.PeriodicPlanar

open Set

noncomputable section

def triHexFKTerminalReachIndicator
    (L : Nat) [Fact (2 < L)] (x : TorusSite L)
    (target : Finset (TorusSite L))
    (sector : TorusSite L → ThreeTerminalConnectivity) : Real := by
  classical
  exact if ∃ y ∈ target,
    (triHexFKTerminalSectorGraph (triHexTorusCellTerminal L) sector).Reachable x y
  then 1 else 0


def triangularTorusActiveReachIndicator
    (L : Nat) [Fact (2 < L)] (x : TorusSite L)
    (target : Finset (TorusSite L))
    (omega : ConfigSpace (triangularTorusGraph L).edgeSet) : Real :=
  if ∃ y ∈ target,
      (openSub (triangularTorusGraph L)
        (extendActive (triangularTorusGraph L) omega)).Reachable x y
    then 1 else 0


def hexagonalTorusActiveWhiteReachIndicator
    (L : Nat) [Fact (2 < L)] (x : TorusSite L)
    (target : Finset (TorusSite L))
    (omega : ConfigSpace (hexagonalTorusGraph L).edgeSet) : Real :=
  if ∃ y ∈ target,
      (openSub (hexagonalTorusGraph L)
        (extendActive (hexagonalTorusGraph L) omega)).Reachable
          (x, true) (y, true)
    then 1 else 0


def triangularTorusActiveReachEvent
    (L : Nat) [Fact (2 < L)] (x : TorusSite L)
    (target : Finset (TorusSite L)) :
    Set (ConfigSpace (triangularTorusGraph L).edgeSet) :=
  {omega | ∃ y ∈ target,
    (openSub (triangularTorusGraph L)
      (extendActive (triangularTorusGraph L) omega)).Reachable x y}


def hexagonalTorusActiveWhiteReachEvent
    (L : Nat) [Fact (2 < L)] (x : TorusSite L)
    (target : Finset (TorusSite L)) :
    Set (ConfigSpace (hexagonalTorusGraph L).edgeSet) :=
  {omega | ∃ y ∈ target,
    (openSub (hexagonalTorusGraph L)
      (extendActive (hexagonalTorusGraph L) omega)).Reachable
        (x, true) (y, true)}

end
end StatMech.FK.PeriodicPlanar
