/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/BaseCase.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib


namespace StatMech.Onsager.BaseCase

open Finset

open Fin.NatCast


def stepOf : Fin 4 → ℤ × ℤ
  | 0 => (1, 0)
  | 1 => (0, 1)
  | 2 => (-1, 0)
  | 3 => (0, -1)


def pos {n : ℕ} [NeZero n] (d : Fin n → Fin 4) (k : Fin n) : ℤ × ℤ :=
  ∑ i ∈ Finset.filter (· < k) Finset.univ, stepOf (d i)


def cc {n : ℕ} [NeZero n] (d : Fin n → Fin 4) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => d (i + 1) - d i = 1)).card


end StatMech.Onsager.BaseCase
