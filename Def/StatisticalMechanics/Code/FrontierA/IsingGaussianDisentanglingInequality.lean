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
import Abbrev.StatisticalMechanics.Code.FrontierA.IsingGaussianDisentanglingInequality
open Finset SimpleGraph
open scoped BigOperators
open Classical

set_option linter.unusedSectionVars false


namespace StatMech.FrontierA

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def finiteTreePairVacuumWeight
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (A : Finset V)
    (pq : (G.edgeFinset -> Nat) × (G.edgeFinset -> Nat)) : Real :=
  (if sources G (ofEdgeFun G pq.1) = A
    then weight G beta J (ofEdgeFun G pq.1) else 0) *
  (if sources G (ofEdgeFun G pq.2) = ∅
    then weight G beta J (ofEdgeFun G pq.2) else 0)

noncomputable def finiteTreeIndependentDisjointSummand
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (i j k l : V)
    (z : DisentangleFourProfiles G) : Real :=
  finiteTreePairVacuumWeight G beta J {i, j} z.1 *
    finiteTreePairVacuumWeight G beta J {k, l} z.2 *
      (if ¬ ∃ y : V,
        CurrentConnected G
          (ofEdgeFun G (fun e => z.1.1 e + z.1.2 e)) i y ∧
        CurrentConnected G
          (ofEdgeFun G (fun e => z.2.1 e + z.2.2 e)) k y
      then 1 else 0)


noncomputable def finiteTreeIndependentDisjointFourCurrentMass
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (i j k l : V) : Real :=
  ∑' z : DisentangleFourProfiles G,
    finiteTreeIndependentDisjointSummand G beta J i j k l z

end StatMech.FrontierA
