/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianNewmanBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianMomentConvergence
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianNewmanBridge
open Filter MeasureTheory Set Topology


namespace StatMech.FrontierA

open ProbabilityTheory


structure NewmanFourthCumulantControl
    (cumulants : Nat -> Nat -> Real) : Prop where
  order_zero : forall scale, cumulants scale 0 = 0
  odd_order : forall scale order, Odd order -> cumulants scale order = 0
  even_order : forall scale halfOrder, 2 <= halfOrder ->
    |cumulants scale (2 * halfOrder)| <=
      (Nat.factorial (2 * halfOrder) : Real) *
        |cumulants scale 4| *
        (1 + |cumulants scale 2|) ^ (halfOrder - 2)


end StatMech.FrontierA
