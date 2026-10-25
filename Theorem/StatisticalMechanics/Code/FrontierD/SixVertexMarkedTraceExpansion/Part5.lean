/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedTraceExpansion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexSectorPerronLogConcavity.Part3
import Mathlib.Algebra.Polynomial.Eval.Degree
import Def.StatisticalMechanics.Code.FrontierD.SixVertexMarkedTraceExpansion.Part5
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

open Polynomial


theorem coeff_sixVertexMarkedFugacityPolynomial
    (N M k n : Nat) (hn : n <= N) :
    (sixVertexMarkedFugacityPolynomial N M k).coeff n =
      sixVertexMarkedSectorTraceCoefficient N M n k := by
  classical
  simp [sixVertexMarkedFugacityPolynomial, Polynomial.coeff_monomial, hn]


end
end StatMech.FrontierD
