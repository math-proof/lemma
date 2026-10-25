/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexCounterexample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneP3Domain
import Instance.StatisticalMechanics.Code.Sharpness.BackboneSupportLexCounterexample.Part2
open Finset


namespace StatMech.Sharpness

def shbK4SelectsDirect03 (A : Finset shbK4Edge) : Prop :=
  shbK4Boundary A = {0, 3} ∧
    shbK4Edge.e03 ∈ A ∧
    ¬ ({shbK4Edge.e01, shbK4Edge.e13} : Finset shbK4Edge) ⊆ A ∧
    ¬ ({shbK4Edge.e01, shbK4Edge.e12, shbK4Edge.e23} :
        Finset shbK4Edge) ⊆ A ∧
    ¬ ({shbK4Edge.e02, shbK4Edge.e12, shbK4Edge.e13} :
        Finset shbK4Edge) ⊆ A ∧
    ¬ ({shbK4Edge.e02, shbK4Edge.e23} : Finset shbK4Edge) ⊆ A

end StatMech.Sharpness
