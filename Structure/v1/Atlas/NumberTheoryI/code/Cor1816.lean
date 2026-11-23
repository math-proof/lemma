/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor1816.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.NumberTheoryI.code.DirichletCharacters
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.DirichletCharacters
public section

open DirichletCharacter


structure PrimCharDvd (R : Type*) [CommMonoidWithZero R] (m : ℕ) where
  d : ℕ
  hdvd : d ∣ m
  χ : DirichletCharacter R d
  hprim : χ.IsPrimitive

