module
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionSymmetricMeanSwitching.Part2
public import Std.Data.TreeMap.Basic
public import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore
open Finset
open Std


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneCertificateCore.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

namespace NOneSymmetricMeanCertificate

open StatMech StatMech.Ising

abbrev BiTermMap := TreeMap (Int × Int) Int biExponentCompare

end NOneSymmetricMeanCertificate
end StatMech.FrontierA
