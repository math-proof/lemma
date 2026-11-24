module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Onsager.InteriorReaches
public import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
public import Theorem.StatisticalMechanics.Code.Onsager.WindingBridge.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WindingBridge.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Onsager.WindingBridge

open StatMech.Lattice

open StatMech.Onsager.ChordCut

open StatMech.Onsager.InteriorReaches


def Bset (S : Set (Site 2)) : Set Pt :=
  {p : Pt | bdEdge S s(toSite p, toSite (p.1 + 1, p.2))}


end StatMech.Onsager.WindingBridge
