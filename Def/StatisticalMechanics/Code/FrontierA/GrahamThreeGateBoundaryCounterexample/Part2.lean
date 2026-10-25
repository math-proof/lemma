/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamThreeGateBoundaryCounterexample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorBalancedCore.Part17
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamThreeGateBoundaryCounterexample
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent


def canonicalGateCounterEnds : Fin 21 -> Sym2 (Fin 7)
  | 0 => s(0, 1)
  | 1 => s(0, 2)
  | 2 => s(0, 3)
  | 3 => s(0, 4)
  | 4 => s(0, 5)
  | 5 => s(0, 6)
  | 6 => s(1, 2)
  | 7 => s(1, 3)
  | 8 => s(1, 4)
  | 9 => s(1, 5)
  | 10 => s(1, 6)
  | 11 => s(2, 3)
  | 12 => s(2, 4)
  | 13 => s(2, 5)
  | 14 => s(2, 6)
  | 15 => s(3, 4)
  | 16 => s(3, 5)
  | 17 => s(3, 6)
  | 18 => s(4, 5)
  | 19 => s(4, 6)
  | 20 => s(5, 6)
  | _ => s(5, 6)

def canonicalGateCounterSupport : Finset (Fin 21) :=
  {0, 2, 5, 6, 13, 14, 15, 16, 17, 18, 20}

def canonicalGateCounterK : Finset (Fin 21) := {0, 13, 14, 20}

def canonicalGateCounterL : Finset (Fin 21) :=
  {2, 5, 6, 15, 16, 17, 18}

def canonicalGateCounterA : Finset (Fin 21) :=
  {0, 6, 13, 14, 15, 16, 18, 20}

def canonicalGateCounterB : Finset (Fin 21) := {2, 5, 17}

def canonicalGateCounterS : Finset (Fin 21) :=
  {0, 13, 14, 15, 16, 18, 20}

def canonicalGateCounterR : Finset (Fin 21) := {2, 5, 6, 17}

def canonicalGateCounterC0 : Finset (Fin 21) := {0, 13, 14, 20}

def canonicalGateCounterC1 : Finset (Fin 21) := ∅

def canonicalGateCounterC2 : Finset (Fin 21) := {6, 15, 16, 18}

def canonicalGateCounterC3 : Finset (Fin 21) := {2, 5, 17}

def canonicalGateCounterTransfer : Finset (Fin 21) := {6}

def CanonicalGateCounterGated (E : Finset (Fin 21)) : Prop :=
  ¬ connK canonicalGateCounterEnds E 1 3 ∧
    ¬ connK canonicalGateCounterEnds (canonicalGateCounterSupport \ E) 1 3

end StatMech.GrahamGHS.FourColor
