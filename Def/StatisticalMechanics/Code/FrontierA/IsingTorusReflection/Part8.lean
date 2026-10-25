/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusGaussianDomination.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusReflection.Part8
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising

variable {d k : Nat}

noncomputable def isingTorusLowerHalfWeight (i : Fin d) (beta : Real)
    (u : IsingTorusLowerSite (k := k) i → Real) : Real :=
  Real.exp (-(beta / 2) * isingTorusDirichlet
    (isingTorusEmbedLower i u))

noncomputable def isingTorusUpperHalfWeight (i : Fin d) (beta : Real)
    (u : IsingTorusLowerSite (k := k) i → Real) : Real :=
  Real.exp (-(beta / 2) * isingTorusDirichlet
    (isingTorusEmbedUpper i u))

end StatMech.FrontierA
