/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangTriangle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangSingleEdge.Part3
import Abbrev.StatisticalMechanics.Code.FrontierA.LeeYangTriangle
open scoped BigOperators
open Finset Polynomial


namespace StatMech.FrontierA

open StatMech.Ising StatMech.FrontierB


def finiteSmallComponentGraph (i e t : ℕ) :
    SimpleGraph (SmallComponentVertex i e t) :=
  (⊥ : SimpleGraph (Fin i)) ⊕g (finiteMatching e ⊕g finiteTriangleGraph t)

end StatMech.FrontierA
