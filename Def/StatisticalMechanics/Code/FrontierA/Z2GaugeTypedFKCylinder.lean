/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinder.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFK.Part14
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugePerimeterReduction.Part4
open scoped BigOperators symmDiff

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech.FrontierA

noncomputable section

variable {P V : Type*} [Fintype P] [DecidableEq P]
  [Fintype V] [DecidableEq V]


def typedBondFirstEndpoints (ends : P -> V × V) (D : Finset P) :
    Finset V :=
  D.image (fun p => (ends p).1)

def typedBondSecondEndpoints (ends : P -> V × V) (D : Finset P) :
    Finset V :=
  D.image (fun p => (ends p).2)

def typedBondVertices (ends : P -> V × V) (D : Finset P) :
    Finset V :=
  typedBondFirstEndpoints ends D ∪ typedBondSecondEndpoints ends D


def typedTrueEndpoint (ends : P -> V × V) (chi : V -> Bool) (p : P) : V :=
  if chi (ends p).1 then (ends p).1 else (ends p).2

def typedFalseEndpoint (ends : P -> V × V) (chi : V -> Bool) (p : P) : V :=
  if chi (ends p).1 then (ends p).2 else (ends p).1

def typedMarkedBondVertices (mark : P -> V) (D : Finset P) : Finset V :=
  D.image mark

end
end StatMech.FrontierA
