/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneCertificateCore.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionSymmetricMeanSwitching.Part2
public import Std.Data.TreeMap.Basic
public section

open Finset
open Std


namespace StatMech.FrontierA

namespace NOneSymmetricMeanCertificate

open StatMech StatMech.Ising

structure BiTerm where
  ex : Int
  ey : Int
  coeff : Int
  deriving DecidableEq, Repr

structure BiPoly where
  terms : List BiTerm
  deriving DecidableEq, Repr

end NOneSymmetricMeanCertificate
end StatMech.FrontierA
