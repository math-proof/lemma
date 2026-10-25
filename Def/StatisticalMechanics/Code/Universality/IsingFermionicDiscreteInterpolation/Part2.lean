/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDiscreteInterpolation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCaratheodoryApproximation.Part3
import Mathlib.Topology.UniformSpace.Ascoli
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDiscreteInterpolation.Part3
open Filter Metric Set Topology
open scoped UniformConvergence


noncomputable section

namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC

namespace FKIsingCaratheodoryApproximation

variable (A : FKIsingCaratheodoryApproximation)


variable (I : A.StableDiscreteInterpolation)


def StableDiscreteInterpolation.SubsequentialMoreraPrimitive
    (target Phi : Complex → Complex) : Prop :=
  ∀ (phi psi : Nat → Nat) (f : Complex → Complex),
    StrictMono phi → StrictMono psi →
    TendstoLocallyUniformlyOn
      (fun n => I.interpolant (phi (psi n))) f atTop A.U →
    Complex.IsConservativeOn f A.U ∧
    ∃ (P : Complex → Complex) (C : Real),
      DifferentiableOn Complex P A.U ∧
      Set.EqOn (deriv P) (fun z => f z ^ 2) A.U ∧
      (∀ z ∈ A.U, (P z).im = (Phi z).im + C) ∧
      f A.root = target A.root


end FKIsingCaratheodoryApproximation
end StatMech.Universality
end
