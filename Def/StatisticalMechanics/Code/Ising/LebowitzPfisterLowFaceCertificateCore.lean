/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceCertificateCore.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Data.List.FinRange
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Tactic
import Structure.StatisticalMechanics.Code.Ising.LebowitzPfisterLowFaceCertificateCore
open Finset


namespace StatMech.Ising

namespace LowFaceCertificate

def TriPoly.insert (t : TriTerm) : List TriTerm -> List TriTerm
  | [] => [t]
  | s :: ss =>
      if t.ex = s.ex ∧ t.ey = s.ey ∧ t.ez = s.ez then
        { s with coeff := s.coeff + t.coeff } :: ss
      else
        s :: insert t ss

def TriPoly.ofTerms (ts : List TriTerm) : TriPoly :=
  ⟨ts.foldl (fun out t => insert t out) []⟩

def TriPoly.const (q : Int) : TriPoly :=
  ⟨[{ ex := 0, ey := 0, ez := 0, coeff := q }]⟩

def TriPoly.add (p q : TriPoly) : TriPoly := .ofTerms (p.terms ++ q.terms)

def TriPoly.neg (p : TriPoly) : TriPoly :=
  ⟨p.terms.map fun t => { t with coeff := -t.coeff }⟩

def TriPoly.mul (p q : TriPoly) : TriPoly :=
  .ofTerms <| p.terms.flatMap fun s => q.terms.map fun t =>
    { ex := s.ex + t.ex, ey := s.ey + t.ey, ez := s.ez + t.ez,
      coeff := s.coeff * t.coeff }

def TriPoly.pow (p : TriPoly) : Nat -> TriPoly
  | 0 => .const 1
  | n + 1 => p.mul (p.pow n)

end LowFaceCertificate
end StatMech.Ising
