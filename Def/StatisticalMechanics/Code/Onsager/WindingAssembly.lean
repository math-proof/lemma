/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WindingAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.GroundUpWinding.Part4
import Theorem.StatisticalMechanics.Code.Onsager.SplitConstruction
import Theorem.StatisticalMechanics.Code.Onsager.PolygonWalk.Part3


namespace StatMech.Onsager.WindingAssembly

open StatMech.Onsager.SplitConstruction


def turn (p q : Pt) : ℤ := StatMech.Onsager.PolygonWalk.cross p q


def turnList (V : List Pt) : List ℤ :=
  let d := List.zipWith (fun p q : Pt => ((q.1 - p.1 : ℤ), (q.2 - p.2 : ℤ))) V (V.rotate 1)
  List.zipWith turn d (d.rotate 1)


def ccCount (V : List Pt) : ℤ := ((turnList V).countP (fun t => t == 1) : ℤ)


def rcCount (V : List Pt) : ℤ := ((turnList V).countP (fun t => t == -1) : ℤ)


def simplePred (V : List Pt) : Prop := V.Nodup ∧ IsClosedWalk isAxisAligned V


end StatMech.Onsager.WindingAssembly
