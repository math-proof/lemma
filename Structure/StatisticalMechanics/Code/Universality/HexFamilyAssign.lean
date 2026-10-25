/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFamilyAssign.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexContourDecomp.Part2
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexFamilyAssign


namespace StatMech.Universality

open Complex

open scoped BigOperators


structure HexFamilyData {V : Type*} [DecidableEq V]
    (D : HexDomain V) (P : D.InteriorPairing) where
  
  cls : HexIncidence V → Fin 5
  
  dirA : ℂ
  
  dirL : ℂ
  
  dirTp : ℂ
  
  dirTm : ℂ
  
  dirU : ℂ
  
  dirEqA : ∀ e ∈ (D.incidences \ P.interior).filter (fun e => cls e = 0),
    D.mid e.vtx e.edge - D.pos e.vtx = dirA
  
  dirEqL : ∀ e ∈ (D.incidences \ P.interior).filter (fun e => cls e = 1),
    D.mid e.vtx e.edge - D.pos e.vtx = dirL
  
  dirEqTp : ∀ e ∈ (D.incidences \ P.interior).filter (fun e => cls e = 2),
    D.mid e.vtx e.edge - D.pos e.vtx = dirTp
  
  dirEqTm : ∀ e ∈ (D.incidences \ P.interior).filter (fun e => cls e = 3),
    D.mid e.vtx e.edge - D.pos e.vtx = dirTm
  
  dirEqU : ∀ e ∈ (D.incidences \ P.interior).filter (fun e => cls e = 4),
    D.mid e.vtx e.edge - D.pos e.vtx = dirU
  
  lam : ℝ
  
  taup : ℝ
  
  taum : ℝ
  
  ups : ℝ
  
  Fa : ℝ
  
  projA : dirA *
      (∑ e ∈ (D.incidences \ P.interior).filter (fun e => cls e = 0), D.obs (D.mid e.vtx e.edge))
      = Complex.I * (((-1 : ℝ) * Fa : ℝ) : ℂ)
  
  projL : dirL *
      (∑ e ∈ (D.incidences \ P.interior).filter (fun e => cls e = 1), D.obs (D.mid e.vtx e.edge))
      = Complex.I * ((hexBdryCl * lam : ℝ) : ℂ)
  
  projTp : dirTp *
      (∑ e ∈ (D.incidences \ P.interior).filter (fun e => cls e = 2), D.obs (D.mid e.vtx e.edge))
      = Complex.I * ((hexBdryCt * taup : ℝ) : ℂ)
  
  projTm : dirTm *
      (∑ e ∈ (D.incidences \ P.interior).filter (fun e => cls e = 3), D.obs (D.mid e.vtx e.edge))
      = Complex.I * ((hexBdryCt * taum : ℝ) : ℂ)
  
  projU : dirU *
      (∑ e ∈ (D.incidences \ P.interior).filter (fun e => cls e = 4), D.obs (D.mid e.vtx e.edge))
      = Complex.I * ((ups : ℝ) : ℂ)

end StatMech.Universality
