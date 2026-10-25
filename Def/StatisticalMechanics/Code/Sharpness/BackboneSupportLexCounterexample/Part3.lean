/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexCounterexample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneP3Domain
import Inductive.StatisticalMechanics.Code.Sharpness.BackboneSupportLexCounterexample.Part2
open Finset


namespace StatMech.Sharpness

def shbK4Path03.edges : shbK4Path03 → Finset shbK4Edge
  | p0123 => {shbK4Edge.e01, shbK4Edge.e12, shbK4Edge.e23}
  | p013 => {shbK4Edge.e01, shbK4Edge.e13}
  | p0213 => {shbK4Edge.e02, shbK4Edge.e12, shbK4Edge.e13}
  | p023 => {shbK4Edge.e02, shbK4Edge.e23}
  | p03 => {shbK4Edge.e03}


def shbK4SupportsPath (A : Finset shbK4Edge) (p : shbK4Path03) : Prop :=
  p.edges ⊆ A

end StatMech.Sharpness
