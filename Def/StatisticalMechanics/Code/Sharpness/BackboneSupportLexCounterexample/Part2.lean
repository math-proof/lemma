/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexCounterexample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneP3Domain
import Instance.StatisticalMechanics.Code.Sharpness.BackboneSupportLexCounterexample
open Finset


namespace StatMech.Sharpness

def shbK4Boundary (A : Finset shbK4Edge) : Finset (Fin 4) :=
  Finset.univ.filter fun v => Odd ((A.filter fun e => e.Incident v).card)


def shbK4Configs (E : Finset shbK4Edge) : Finset (Finset shbK4Edge) :=
  E.powerset


def shbK4H : Finset shbK4Edge :=
  {shbK4Edge.e01, shbK4Edge.e02, shbK4Edge.e03,
    shbK4Edge.e13, shbK4Edge.e23}


def shbK4G : Finset shbK4Edge := Finset.univ


end StatMech.Sharpness
