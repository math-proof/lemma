/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexContourDecomp.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexBoundary.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexContourDecomp


namespace StatMech.Universality

open Complex

open scoped BigOperators


structure HexBoundaryDecomp {V : Type*} [DecidableEq V]
    (D : HexDomain V) (P : D.InteriorPairing) where
  
  A : HexSide D
  
  L : HexSide D
  
  Tp : HexSide D
  
  Tm : HexSide D
  
  U : HexSide D
  
  lam : ℝ
  
  taup : ℝ
  
  taum : ℝ
  
  ups : ℝ
  
  Fa : ℝ
  
  partition : D.incidences \ P.interior =
    A.cells ∪ L.cells ∪ Tp.cells ∪ Tm.cells ∪ U.cells
  
  disjAL : Disjoint A.cells L.cells
  disjATp : Disjoint A.cells Tp.cells
  disjATm : Disjoint A.cells Tm.cells
  disjAU : Disjoint A.cells U.cells
  disjLTp : Disjoint L.cells Tp.cells
  disjLTm : Disjoint L.cells Tm.cells
  disjLU : Disjoint L.cells U.cells
  disjTpTm : Disjoint Tp.cells Tm.cells
  disjTpU : Disjoint Tp.cells U.cells
  disjTmU : Disjoint Tm.cells U.cells
  
  projA : A.dir * A.fSum = Complex.I * (((-1 : ℝ) * Fa : ℝ) : ℂ)
  
  projL : L.dir * L.fSum = Complex.I * ((hexBdryCl * lam : ℝ) : ℂ)
  
  projTp : Tp.dir * Tp.fSum = Complex.I * ((hexBdryCt * taup : ℝ) : ℂ)
  
  projTm : Tm.dir * Tm.fSum = Complex.I * ((hexBdryCt * taum : ℝ) : ℂ)
  
  projU : U.dir * U.fSum = Complex.I * ((ups : ℝ) : ℂ)

end StatMech.Universality
