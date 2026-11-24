module
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneRawGenerated
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneLayerCode.Part2
public import Std.Data.TreeMap.Lemmas
public import Std.Data.DTreeMap.Internal.Lemmas
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOnePolynomialSemantics
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
