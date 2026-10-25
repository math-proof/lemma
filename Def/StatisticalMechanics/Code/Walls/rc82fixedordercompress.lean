/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc82fixedordercompress.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc81shifttomonotone.Part3
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


def rc82_pushDown (i : ι) (w : ConfigSpace ι) : ConfigSpace ι := Function.update w i false

def rc82_pushUp (i : ι) (w : ConfigSpace ι) : ConfigSpace ι := Function.update w i true


def rc82_downMap (i : ι) (A : Finset (ConfigSpace ι)) (w : ConfigSpace ι) : ConfigSpace ι :=
  if w i = true ∧ rc82_pushDown i w ∉ A then rc82_pushDown i w else w


def rc82_upMap (i : ι) (B : Finset (ConfigSpace ι)) (w : ConfigSpace ι) : ConfigSpace ι :=
  if w i = false ∧ rc82_pushUp i w ∉ B then rc82_pushUp i w else w


def rc82_downCompressA (i : ι) (A : Finset (ConfigSpace ι)) : Finset (ConfigSpace ι) :=
  A.image (rc82_downMap i A)


def rc82_upCompressB (i : ι) (B : Finset (ConfigSpace ι)) : Finset (ConfigSpace ι) :=
  B.image (rc82_upMap i B)


end StatMech.Walls
