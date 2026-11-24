module
public import Def.StatisticalMechanics.Code.FrontierD.SixVertexAntiferroelectricSeries.Part9
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheThermodynamicReduction.Part4
open Finset Matrix Filter Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheThermodynamicReduction.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

def SixVertexHasIteratedLimit (F : ℕ → ℕ → ℝ) (a : ℝ) : Prop :=
  ∃ g : ℕ → ℝ, (∀ k, Tendsto (F k) atTop (nhds (g k))) ∧
    Tendsto g atTop (nhds a)


end StatMech.FrontierD
