/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryIdentityClose.Part3
import Def.StatisticalMechanics.Code.Universality.HexContourDefs.Part2
import Theorem.StatisticalMechanics.Code.Universality.HexFiniteRegion.Part4
import Def.StatisticalMechanics.Code.Universality.HexFiniteStripBoundary


namespace StatMech.Universality

open Complex HexWalk

open scoped BigOperators

variable {V : Type*} [DecidableEq V]


structure HexFiniteStripBoundaryData (R : HexFiniteRegion) (h0 : ℤ)
    (D : HexDomain V) (P : D.InteriorPairing) where
  
  sides : HexContourSides
  
  interior_sub : P.interior ⊆ D.incidences
  
  vertex_mem : ∀ v ∈ D.interiorVertices, D.pos v ∈ R.verts
  
  mid_mem : ∀ e ∈ D.incidences, D.mid e.vtx e.edge ∈ R.mids
  
  obs_eq : ∀ z, D.obs z =
    parafObservable R.inRegion R.start h0 z (5 / 8) hexChi
  
  lam : ℝ
  
  tau : ℝ
  
  ups : ℝ
  
  Fa : ℝ
  
  lam_eq : lam = hexContourLambda R.inRegion R.start h0 sides hexChi
  
  tau_eq : tau = hexContourTauPlus R.inRegion R.start h0 sides hexChi
    + hexContourTauMinus R.inRegion R.start h0 sides hexChi
  
  ups_eq : ups = hexContourUpsilon R.inRegion R.start h0 sides hexChi
  
  Fa_eq : (Fa : ℂ) = D.obs R.start
  
  alphaRest : ℂ
  alphaRest_eq : alphaRest
    = (Complex.exp ((-(hbi_sigma * Real.pi) : ℝ) * Complex.I)
        + Complex.exp ((hbi_sigma * Real.pi : ℝ) * Complex.I)) / 2 * (lam : ℂ)
  
  betaSum : ℂ
  betaSum_eq : betaSum = (ups : ℂ)
  
  epsSum : ℂ
  epsSum_eq : epsSum
    = Complex.exp ((-(hbi_sigma * (2 * Real.pi / 3)) : ℝ) * Complex.I)
        * ((tau / 2 : ℝ) : ℂ)
  
  epsbarSum : ℂ
  epsbarSum_eq : epsbarSum
    = Complex.exp ((hbi_sigma * (2 * Real.pi / 3) : ℝ) * Complex.I)
        * ((tau / 2 : ℝ) : ℂ)
  
  contour_eq : D.boundarySum P =
    hexFiniteStripRaw Fa alphaRest betaSum epsSum epsbarSum

end StatMech.Universality
