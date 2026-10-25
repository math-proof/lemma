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
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOnePolynomialSemantics.Part4
open Finset
open Std
open scoped Std.DTreeMap.Internal.Impl


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

def shiftedTermExpansion (t : BiTerm) : List BiTerm :=
  (List.range (Int.toNat t.ex + 1)).flatMap fun (a : Nat) =>
      (List.range (Int.toNat t.ey + 1)).map fun (b : Nat) =>
        { ex := (a : Int), ey := (b : Int),
          coeff := t.coeff * ((Int.toNat t.ex).choose a : Int) *
            ((Int.toNat t.ey).choose b : Int) }

end StatMech.FrontierA.NOneSymmetricMeanCertificate
