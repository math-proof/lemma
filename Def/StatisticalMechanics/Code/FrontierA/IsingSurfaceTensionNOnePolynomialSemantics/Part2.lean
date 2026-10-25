/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOnePolynomialSemantics.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneRawGenerated
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneLayerCode.Part2
import Std.Data.TreeMap.Lemmas
import Std.Data.DTreeMap.Internal.Lemmas
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOnePolynomialSemantics.Part2
open Finset
open Std
open scoped Std.DTreeMap.Internal.Impl


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

noncomputable def evalYSquareDivisionInvariant (X Y : Real)
    (qr : BiPoly × BiPoly) : Real :=
  qr.1.eval X Y * (Y ^ 2 - 1) + qr.2.eval X Y

end StatMech.FrontierA.NOneSymmetricMeanCertificate
