/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFaithfulExclusive.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.TwoDim.ZhangHarris.Part7
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Def.StatisticalMechanics.Code.TwoDim.ZhangFaithfulExclusive
open MeasureTheory Set SimpleGraph
open scoped ENNReal NNReal


namespace StatMech.TwoDim

open StatMech.Lattice StatMech.Universality StatMech.Percolation

open StatMech.RSW.Box


theorem zfe_primalEmb_mid_adj {p q : Site 2}
    (h : (hypercubicLattice 2).Adj p q) :
    (hypercubicLattice 2).Adj (zfe_primalEmb p) (zfe_primalMid p q) := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at h ⊢
  simp only [zfe_primalEmb, zfe_primalMid, Matrix.cons_val_zero, Matrix.cons_val_one]
  omega

theorem zfe_primalMid_emb_adj {p q : Site 2}
    (h : (hypercubicLattice 2).Adj p q) :
    (hypercubicLattice 2).Adj (zfe_primalMid p q) (zfe_primalEmb q) := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at h ⊢
  simp only [zfe_primalEmb, zfe_primalMid, Matrix.cons_val_zero, Matrix.cons_val_one]
  omega

theorem zfe_faceEmb_mid_adj {f g : Site 2}
    (h : (hypercubicLattice 2).Adj f g) :
    (hypercubicLattice 2).Adj (zfe_faceEmb f) (zfe_faceMid f g) := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at h ⊢
  simp only [zfe_faceEmb, zfe_faceMid, Matrix.cons_val_zero, Matrix.cons_val_one]
  omega

theorem zfe_faceMid_emb_adj {f g : Site 2}
    (h : (hypercubicLattice 2).Adj f g) :
    (hypercubicLattice 2).Adj (zfe_faceMid f g) (zfe_faceEmb g) := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at h ⊢
  simp only [zfe_faceEmb, zfe_faceMid, Matrix.cons_val_zero, Matrix.cons_val_one]
  omega


end StatMech.TwoDim
