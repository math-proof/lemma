/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SplitConstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Abbrev.StatisticalMechanics.Code.Onsager.SplitConstruction


namespace StatMech.Onsager.SplitConstruction

open List

def isAxisAligned (p q : Pt) : Prop := p.1 = q.1 ∨ p.2 = q.2


def isUnitStep (p q : Pt) : Prop := (p.1 - q.1).natAbs + (p.2 - q.2).natAbs = 1


def IsClosedWalk (R : Pt → Pt → Prop) (L : List Pt) : Prop :=
  List.IsChain R L ∧ ∀ x ∈ L.getLast?, ∀ y ∈ L.head?, R x y


def arc (V : List Pt) (a b : ℕ) : List Pt := (V.drop a).take (b - a + 1)


def coarc (V : List Pt) (a b : ℕ) : List Pt := V.drop b ++ V.take (a + 1)


end StatMech.Onsager.SplitConstruction
