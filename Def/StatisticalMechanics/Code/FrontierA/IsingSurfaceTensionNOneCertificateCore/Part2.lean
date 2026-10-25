/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneCertificateCore.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionSymmetricMeanSwitching.Part2
import Std.Data.TreeMap.Basic
import Abbrev.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore
open Finset
open Std


namespace StatMech.FrontierA

namespace NOneSymmetricMeanCertificate

open StatMech StatMech.Ising

def BiPoly.ofTerms (ts : List BiTerm) : BiPoly :=
  let m : BiTermMap := ts.foldl (fun (out : BiTermMap) (t : BiTerm) =>
    out.alter (t.ex, t.ey) fun (o : Option Int) => match o with
      | none => if t.coeff = 0 then none else some (t.coeff : Int)
      | some (c : Int) =>
          if c + t.coeff = 0 then none else some (c + t.coeff))
    (TreeMap.empty : BiTermMap)
  ⟨m.toList.map fun t => { ex := t.1.1, ey := t.1.2, coeff := t.2 }⟩

def BiPoly.monomial (ex ey : Int) (coeff : Int) : BiPoly :=
  .ofTerms [{ ex := ex, ey := ey, coeff := coeff }]

def BiPoly.add (p q : BiPoly) : BiPoly :=
  .ofTerms (p.terms ++ q.terms)

def BiPoly.neg (p : BiPoly) : BiPoly :=
  .ofTerms (p.terms.map fun t => { t with coeff := -t.coeff })

def BiPoly.sub (p q : BiPoly) : BiPoly := p.add q.neg

def BiPoly.mul (p q : BiPoly) : BiPoly :=
  .ofTerms <| p.terms.flatMap fun s => q.terms.map fun t =>
    { ex := s.ex + t.ex, ey := s.ey + t.ey,
      coeff := s.coeff * t.coeff }

end NOneSymmetricMeanCertificate
end StatMech.FrontierA
