module
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneRawGenerated
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneLayerCode.Part2
public import Std.Data.TreeMap.Lemmas
public import Std.Data.DTreeMap.Internal.Lemmas
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOnePolynomialSemantics.Part3
open Finset
open Std
open scoped Std.DTreeMap.Internal.Impl


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOnePolynomialSemantics.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

noncomputable def evalXSquareDivisionInvariant (X Y : Real)
    (qr : BiPoly × BiPoly) : Real :=
  qr.1.eval X Y * (X ^ 2 - 1) + qr.2.eval X Y

end StatMech.FrontierA.NOneSymmetricMeanCertificate
