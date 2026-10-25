/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeEndpointZero
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterLowFaceCertificate
open Finset


namespace StatMech.Ising

open StatMech.FrontierA

open StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace LowFaceCertificate

def TriTerm.eval (t : TriTerm) (x y z : Real) : Real :=
  t.coeff * x ^ t.ex * y ^ t.ey * z ^ t.ez

def evalTerms : List TriTerm -> Real -> Real -> Real -> Real
  | [], _, _, _ => 0
  | t :: ts, x, y, z => t.eval x y z + evalTerms ts x y z

def TriPoly.eval (p : TriPoly) (x y z : Real) : Real :=
  evalTerms p.terms x y z

end LowFaceCertificate
end
end StatMech.Ising
