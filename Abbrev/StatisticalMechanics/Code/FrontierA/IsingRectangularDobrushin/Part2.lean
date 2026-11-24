module
public import Theorem.StatisticalMechanics.Code.Ising.PressureBCIndep
public import Theorem.StatisticalMechanics.Code.Ising.MonomialDisorder
public import Def.StatisticalMechanics.Code.FrontierA.IsingRectangularDobrushin
open scoped BigOperators
open Finset


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingRectangularDobrushin.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Ising

noncomputable section

abbrev RectangularPrismInteraction (m n h : Nat) :=
  (Fin (m - 1) × Fin n × Fin (2 * h + 1)) ⊕
    ((Fin m × Fin (n - 1) × Fin (2 * h + 1)) ⊕
      ((Fin m × Fin n × Fin (2 * h)) ⊕ RectangularPrismSite m n h))

end
end StatMech.Ising
