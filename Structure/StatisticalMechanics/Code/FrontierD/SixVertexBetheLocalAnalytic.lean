/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheLocalAnalytic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheAnalyticContinuation.Part2
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Topology.Homotopy.Affine
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheLocalAnalytic.Part6
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

structure SixVertexLocalAnalyticBetheBranch
    (N n : Nat) (c : Real) (p : Fin n → Real) where
  roots : Real → (Fin n → Real)
  analyticAt_roots : AnalyticAt Real roots c
  roots_at : roots c = p
  eventually_solution : ∀ᶠ t in 𝓝 c,
    SixVertexSatisfiesBetheEquations t N n (roots t)
  eventually_unique : ∀ᶠ q : Real × (Fin n → Real) in 𝓝 (c, p),
    SixVertexSatisfiesBetheEquations q.1 N n q.2 → roots q.1 = q.2


end
end StatMech.FrontierD
