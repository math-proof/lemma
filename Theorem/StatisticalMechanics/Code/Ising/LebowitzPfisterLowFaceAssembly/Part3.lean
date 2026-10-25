/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeEndpointZero
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterLowFaceCertificate
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterLowFaceAssembly.Part3
open Finset


namespace StatMech.Ising

open StatMech.FrontierA

open StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace LowFaceCertificate

lemma foldl_radialTermCoeff (ts : List TriTerm) (q : Int)
    (a : Fin 13) (b : Fin 8) (c : Fin 4) :
    ts.foldl (fun q t => q + radialTermCoeff t a b c) q =
      q + radialCoeffTerms ts a b c := by
  induction ts generalizing q with
  | nil => simp [radialCoeffTerms]
  | cons t ts ih =>
      rw [List.foldl_cons, ih]
      simp [radialCoeffTerms]
      ring

lemma radialBernCoeffOf_eq (p : TriPoly) (a : Fin 13) (b : Fin 8) (c : Fin 4) :
    radialBernCoeffOf p a b c = radialCoeffTerms p.terms a b c := by
  rw [radialBernCoeffOf, show
    (fun q t => q + t.coeff * scaledBernFactor 12 27720 t.ex a *
      scaledBernFactor 7 105 t.ey b * scaledBernFactor 3 3 t.ez c) =
    (fun q t => q + radialTermCoeff t a b c) by rfl,
    foldl_radialTermCoeff]
  simp

end LowFaceCertificate
end
end StatMech.Ising
