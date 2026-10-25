/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianDisentanglingInequality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianClusterConfinement.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianIntersectionUnionBound.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamWeightedAuxiliaryAlgebra
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianDisentanglingInequality
open Finset SimpleGraph
open scoped BigOperators
open Classical

set_option linter.unusedSectionVars false


namespace StatMech.FrontierA

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def finiteTreeDisjointComponentSummand
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (i j k l : V)
    (S : Finset V) (z : DisentangleFourProfiles G) : Real :=
  finiteTreePairVacuumWeight G beta J {i, j} z.1 *
    finiteTreePairVacuumWeight G beta J {k, l} z.2 *
      (if notConnComp G
          (ofEdgeFun G (fun e => z.1.1 e + z.1.2 e)) i = S ∧
        k ∈ finiteTreeSafeRegion G
          (ofEdgeFun G (fun e => z.2.1 e + z.2.2 e)) Sᶜ
      then 1 else 0)

end StatMech.FrontierA
