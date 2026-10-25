/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusCharacter.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusGaussianDomination.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.IsingInfraredReduction
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Def.StatisticalMechanics.Code.FrontierA.IsingTorusCharacter
open Finset
open scoped BigOperators ComplexConjugate


namespace StatMech.FrontierA

open StatMech.Ising

variable {d k : Nat}


theorem isingTorusCharacterDispersion_nonneg
    (chi : AddChar (IsingDyadicTorus d k) Complex) :
    0 ≤ isingTorusCharacterDispersion chi := by
  exact Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

theorem character_edge_normSq
    (chi : AddChar (IsingDyadicTorus d k) Complex)
    (x : IsingDyadicTorus d k) (i : Fin d) :
    Complex.normSq (chi x - chi (x + isingTorusStep i)) =
      Complex.normSq (1 - chi (isingTorusStep i)) := by
  rw [AddChar.map_add_eq_mul]
  rw [show chi x - chi x * chi (isingTorusStep i) =
      chi x * (1 - chi (isingTorusStep i)) by ring,
    Complex.normSq_mul]
  rw [Complex.normSq_eq_norm_sq, AddChar.norm_apply, one_pow, one_mul]


theorem isingTorusDirichlet_re_add_im_addChar
    (chi : AddChar (IsingDyadicTorus d k) Complex) :
    isingTorusDirichlet (fun x => (chi x).re) +
        isingTorusDirichlet (fun x => (chi x).im) =
      Fintype.card (IsingDyadicTorus d k) *
        isingTorusCharacterDispersion chi := by
  unfold isingTorusDirichlet isingTorusDirichletBilinear
  rw [← Finset.sum_add_distrib]
  calc
    ∑ x : IsingDyadicTorus d k,
        ((∑ i : Fin d,
            ((chi x).re - (chi (x + isingTorusStep i)).re) *
              ((chi x).re - (chi (x + isingTorusStep i)).re)) +
          ∑ i : Fin d,
            ((chi x).im - (chi (x + isingTorusStep i)).im) *
              ((chi x).im - (chi (x + isingTorusStep i)).im)) =
        ∑ x : IsingDyadicTorus d k, ∑ i : Fin d,
          Complex.normSq (chi x - chi (x + isingTorusStep i)) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    _ = ∑ _x : IsingDyadicTorus d k, ∑ i : Fin d,
          Complex.normSq (1 - chi (isingTorusStep i)) := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro i _
      exact character_edge_normSq chi x i
    _ = Fintype.card (IsingDyadicTorus d k) *
          isingTorusCharacterDispersion chi := by
      simp [isingTorusCharacterDispersion]


end StatMech.FrontierA
