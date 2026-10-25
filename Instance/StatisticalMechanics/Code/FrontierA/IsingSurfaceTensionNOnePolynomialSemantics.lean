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
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOnePolynomialSemantics
open Finset
open Std
open scoped Std.DTreeMap.Internal.Impl


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

instance : TransCmp biExponentCompare := by
  rw [biExponentCompare_eq_compareLex]
  infer_instance

instance : LawfulEqCmp biExponentCompare := by
  refine { eq_of_compare := ?_ }
  intro a b h
  simp only [biExponentCompare_eq_compareLex, compareLex_eq_eq,
    compareOn, LawfulEqCmp.compare_eq_iff_eq] at h
  exact Prod.ext h.1 h.2

end StatMech.FrontierA.NOneSymmetricMeanCertificate
