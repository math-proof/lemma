/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneCertificateCore.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionSymmetricMeanSwitching.Part2
import Std.Data.TreeMap.Basic
import Structure.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore
open Finset
open Std


namespace StatMech.FrontierA

namespace NOneSymmetricMeanCertificate

open StatMech StatMech.Ising

def BiPoly.insert (t : BiTerm) : List BiTerm -> List BiTerm
  | [] => if t.coeff = 0 then [] else [t]
  | s :: ss =>
      if t.ex = s.ex && t.ey = s.ey then
        let c := s.coeff + t.coeff
        if c = 0 then ss else { s with coeff := c } :: ss
      else
        s :: insert t ss

def biExponentCompare (a b : Int × Int) : Ordering :=
  match compare a.1 b.1 with
  | .eq => compare a.2 b.2
  | o => o

end NOneSymmetricMeanCertificate
end StatMech.FrontierA
