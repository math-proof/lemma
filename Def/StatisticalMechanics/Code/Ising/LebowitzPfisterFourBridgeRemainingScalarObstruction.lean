/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeRemainingScalarObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeSecondMiddleLowRank


namespace StatMech.Ising

noncomputable section

def FourBridgeEstablishedAggregateRegion (a b c d : Real) : Prop :=
  0 <= a ∧ a <= 4 ∧ 0 <= b ∧ b <= 6 ∧ 0 <= c ∧ c <= 4 ∧
  0 <= d ∧ d <= 1 ∧
  a ^ 3 - 3 * a * b - a + 3 * c <= 0 ∧
  a * d <= c ∧ c * d <= a ∧ a * c <= 2 * b + 4 * d ∧
  a * b <= 3 * (a + c) ∧ b * c <= 3 * (a + c) ∧
  3 * a <= 6 + b ∧ 3 * c <= 6 + b ∧ b ^ 2 <= 5 * b + 6 * d ∧
  0 <= fourBridgeRankMass a b c d 0 ∧
  0 <= fourBridgeRankMass a b c d 1 ∧
  0 <= fourBridgeRankMass a b c d 2 ∧
  0 <= fourBridgeRankMass a b c d 3 ∧
  0 <= fourBridgeRankMass a b c d 4 ∧
  fourBridgeRankMass a b c d 0 * fourBridgeRankMass a b c d 3 <=
    fourBridgeRankMass a b c d 1 * fourBridgeRankMass a b c d 4 ∧
  fourBridgeRankMass a b c d 1 ^ 2 <=
    fourBridgeRankMass a b c d 1 +
      2 * fourBridgeRankMass a b c d 0 * fourBridgeRankMass a b c d 2 ∧
  fourBridgeRankMass a b c d 3 ^ 2 <=
    fourBridgeRankMass a b c d 3 +
      2 * fourBridgeRankMass a b c d 2 * fourBridgeRankMass a b c d 4

def fourBridgeRemainingCounterexampleA : Real := 8 / 5

def fourBridgeRemainingCounterexampleB : Real := 25 / 8

def fourBridgeRemainingCounterexampleC : Real := 64 / 25

def fourBridgeRemainingCounterexampleD : Real := 1 / 20


end
end StatMech.Ising
