/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/RepresentationTheory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RepresentationTheory.Maschke
public import Mathlib.RepresentationTheory.Character
public import Mathlib.RepresentationTheory.FDRep
public import Mathlib.RepresentationTheory.AlgebraRepresentation.Basic
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

namespace RepresentationTheory

open Representation

universe u

def IsIrreducible {k G V : Type*} [Field k] [Group G]
    [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) : Prop :=
  IsSimpleOrder (Subrepresentation ρ)

noncomputable def characterOf {k G V : Type*} [Field k] [Monoid G]
    [AddCommGroup V] [Module k V] (ρ : Representation k G V) : G → k :=
  ρ.character

noncomputable def directSumPair {k G V W : Type*} [Semiring k] [Monoid G]
    [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
    (ρV : Representation k G V) (ρW : Representation k G W) :
    Representation k G (V × W) :=
  Representation.prod ρV ρW

end RepresentationTheory
