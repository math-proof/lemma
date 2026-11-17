/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/NoDoubleWind2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib
public import Theorem.StatisticalMechanics.Code.Onsager.NoDoubleWind
public import Theorem.StatisticalMechanics.Code.Onsager.NoDoubleWind2

@[expose] public section

namespace StatMech.Onsager.NoDoubleWind2

open Finset

open StatMech.Onsager.BaseCase

open StatMech.Onsager.NoDoubleWind

variable {n : ℕ} [NeZero n]


def tcount (d : Fin n → Fin 4) (c : Fin 4) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => d i = c ∧ d (i + 1) = c + 1)).card


def scount (d : Fin n → Fin 4) (c : Fin 4) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => d i = c ∧ d (i + 1) = c)).card


end StatMech.Onsager.NoDoubleWind2
