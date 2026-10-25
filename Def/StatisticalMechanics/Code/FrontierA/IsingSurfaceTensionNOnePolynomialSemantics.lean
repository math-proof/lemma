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
import Instance.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOnePolynomialSemantics
open Finset
open Std
open scoped Std.DTreeMap.Internal.Impl


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

noncomputable def BiTerm.eval (X Y : Real) (t : BiTerm) : Real :=
  (t.coeff : Real) * X ^ t.ex * Y ^ t.ey

noncomputable def BiPoly.eval (X Y : Real) (p : BiPoly) : Real :=
  (p.terms.map (BiTerm.eval X Y)).sum

noncomputable def termMapEval (X Y : Real) (m : BiTermMap) : Real :=
  (m.toList.map fun t =>
    (t.2 : Real) * X ^ t.1.1 * Y ^ t.1.2).sum

def addCoefficientOption (d : Int) : Option Int -> Option Int
  | none => if d = 0 then none else some d
  | some c => if c + d = 0 then none else some (c + d)

def addTermToMap (m : BiTermMap) (t : BiTerm) : BiTermMap :=
  m.alter (t.ex, t.ey) (addCoefficientOption t.coeff)

noncomputable def modelEntryEval (X Y : Real)
    (e : (k : Int × Int) × (fun _ => Int) k) : Real :=
  (e.2 : Real) * X ^ e.1.1 * Y ^ e.1.2

end StatMech.FrontierA.NOneSymmetricMeanCertificate
