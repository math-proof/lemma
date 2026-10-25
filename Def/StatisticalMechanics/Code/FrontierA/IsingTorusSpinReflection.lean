/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusSpinReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusGraph.Part4
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Algebra.QuadraticDiscriminant
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising

variable {d k : Nat}


noncomputable def isingTorusHalfReflectionForm
    (i : Fin d) (beta : Real)
    (F G : ConfigSpace (IsingTorusLowerSite (k := k) i) → Real) : Real :=
  ∑ lower : ConfigSpace (IsingTorusLowerSite (k := k) i),
    ∑ upper : ConfigSpace (IsingTorusLowerSite (k := k) i),
      (isingTorusLowerHalfWeight i beta
          (isingTorusLowerValues i 0 lower) * F lower) *
        (isingTorusLowerHalfWeight i beta
          (isingTorusLowerValues i 0 upper) * G upper) *
        Real.exp (beta *
          ∑ e : IsingTorusDirectedEdge d k,
            isingTorusBoundaryFeature i
                (isingTorusLowerValues i 0 lower) e *
              isingTorusBoundaryFeature i
                (isingTorusLowerValues i 0 upper) e)

end StatMech.FrontierA
