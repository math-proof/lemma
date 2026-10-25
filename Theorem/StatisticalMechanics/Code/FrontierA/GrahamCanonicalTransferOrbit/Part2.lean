/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferOrbit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorCollisionStableSelector
import Mathlib.Data.Prod.Lex
import Def.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferOrbit.Part2
open Finset


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem canonicalMaskTransferOrbit_refl
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c : leftMaskFiber ends m j k l zero p) :
    CanonicalMaskTransferOrbit ends m j k l zero p c c :=
  Relation.ReflTransGen.refl

theorem canonicalMaskTransferOrbit_symm
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) :
    Symmetric (CanonicalMaskTransferOrbit ends m j k l zero p) :=
  Relation.ReflTransGen.symmetric
    (canonicalMaskTransferAdjacent_symm ends m j k l zero p)

theorem canonicalMaskTransferOrbit_trans
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) :
    Transitive (CanonicalMaskTransferOrbit ends m j k l zero p) := by
  intro a b c hab hbc
  exact hab.trans hbc


end StatMech.GrahamGHS.FourColor
