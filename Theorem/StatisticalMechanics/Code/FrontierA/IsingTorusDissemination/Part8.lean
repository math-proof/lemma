/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusDissemination.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusReflection.Part10
import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusCharacter.Part3
import Def.StatisticalMechanics.Code.FrontierA.IsingTorusDissemination.Part8
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising

variable {d k : Nat}


theorem isingTorus_indexed_max_disseminate_coordinates
    (beta : Real) (hbeta : 0 ≤ beta)
    (h : IsingDyadicTorus d k → Real)
    (gmax : IsingDyadicTorus d k → IsingDyadicTorus d k)
    (hmax : ∀ g' : IsingDyadicTorus d k → IsingDyadicTorus d k,
      isingTorusShiftedPartition beta (isingTorusIndexedField h g') ≤
        isingTorusShiftedPartition beta (isingTorusIndexedField h gmax)) :
    ∀ S : Finset (Fin d),
      ∃ g : IsingDyadicTorus d k → IsingDyadicTorus d k,
        isingTorusShiftedPartition beta (isingTorusIndexedField h g) =
            isingTorusShiftedPartition beta (isingTorusIndexedField h gmax) ∧
          IsingTorusDisseminatedBox (isingTorusCompletedBoxSides k S)
            (isingTorusIndexedField h g) := by
  intro S
  induction S using Finset.induction with
  | empty =>
      refine ⟨gmax, rfl, ?_⟩
      simpa [isingTorusCompletedBoxSides] using
        (isingTorusDisseminatedBox_one (isingTorusIndexedField h gmax))
  | @insert i S hi ih =>
      obtain ⟨g, hg, hbox⟩ := ih
      have hstart : IsingTorusDisseminatedBox
          (Function.update (isingTorusCompletedBoxSides k S) i 1)
          (isingTorusIndexedField h g) := by
        have hsides0 : Function.update (isingTorusCompletedBoxSides k S) i 1 =
            isingTorusCompletedBoxSides k S := by
          funext j
          by_cases hji : j = i
          · subst j
            simp [isingTorusCompletedBoxSides, hi]
          · simp [hji]
        rw [hsides0]
        exact hbox
      obtain ⟨g', hg', hg'box⟩ :=
        isingTorus_indexed_max_disseminate_coordinate beta hbeta h
          gmax g hmax hg (isingTorusCompletedBoxSides k S) i hstart
          (k + 2) (le_refl _)
      refine ⟨g', hg', ?_⟩
      have hsides : Function.update (isingTorusCompletedBoxSides k S) i
          (2 ^ (k + 2)) = isingTorusCompletedBoxSides k (insert i S) := by
        funext j
        by_cases hji : j = i
        · subst j
          simp [isingTorusCompletedBoxSides]
        · simp [isingTorusCompletedBoxSides, hji]
      rw [← hsides]
      exact hg'box

theorem isingTorusShiftedPartition_eq_zero_of_constant
    (beta : Real) (h : IsingDyadicTorus d k → Real)
    (hconst : ∀ x, h x = h 0) :
    isingTorusShiftedPartition beta h =
      isingTorusShiftedPartition (d := d) (k := k) beta 0 := by
  unfold isingTorusShiftedPartition
  apply Finset.sum_congr rfl
  intro sigma _
  congr 2
  unfold isingTorusDirichlet isingTorusDirichletBilinear
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.add_apply, Pi.zero_apply]
  rw [hconst x, hconst (x + isingTorusStep i)]
  ring


theorem isingTorus_gaussianDominated
    (beta : Real) (hbeta : 0 ≤ beta) :
    IsingTorusGaussianDominated (d := d) (k := k) beta := by
  intro h
  obtain ⟨gmax, -, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun g : IsingDyadicTorus d k → IsingDyadicTorus d k =>
      isingTorusShiftedPartition beta (isingTorusIndexedField h g))
    Finset.univ_nonempty
  have hmax' : ∀ g : IsingDyadicTorus d k → IsingDyadicTorus d k,
      isingTorusShiftedPartition beta (isingTorusIndexedField h g) ≤
        isingTorusShiftedPartition beta (isingTorusIndexedField h gmax) := by
    intro g
    exact hmax g (by simp)
  obtain ⟨gconst, hgconst, hbox⟩ :=
    isingTorus_indexed_max_disseminate_coordinates beta hbeta h gmax hmax'
      Finset.univ
  have hconst : ∀ x, isingTorusIndexedField h gconst x =
      isingTorusIndexedField h gconst 0 := by
    intro x
    apply hbox x
    intro i
    simpa [isingTorusCompletedBoxSides] using (x i).val_lt
  have hidentity : isingTorusIndexedField h id = h := by rfl
  calc
    isingTorusShiftedPartition beta h =
        isingTorusShiftedPartition beta (isingTorusIndexedField h id) := by
          rw [hidentity]
    _ ≤ isingTorusShiftedPartition beta
        (isingTorusIndexedField h gmax) := hmax' id
    _ = isingTorusShiftedPartition beta
        (isingTorusIndexedField h gconst) := hgconst.symm
    _ = isingTorusShiftedPartition (d := d) (k := k) beta 0 :=
      isingTorusShiftedPartition_eq_zero_of_constant beta _ hconst


theorem isingTorus_addChar_secondMoment_le_unconditional
    (beta : Real) (hbeta : 0 < beta)
    (chi : AddChar (IsingDyadicTorus d k) Complex)
    (hdisp : 0 < isingTorusCharacterDispersion chi) :
    (∑ sigma : ConfigSpace (IsingDyadicTorus d k),
        Real.exp (-(beta / 2) *
          isingTorusDirichlet (isingTorusSpinField sigma)) *
        Complex.normSq (∑ x : IsingDyadicTorus d k,
          (isingTorusSpinField sigma x : Complex) * chi x)) ≤
      isingTorusShiftedPartition (d := d) (k := k) beta 0 *
        (Fintype.card (IsingDyadicTorus d k) /
          (beta * isingTorusCharacterDispersion chi)) := by
  exact isingTorus_addChar_secondMoment_le beta hbeta
    (isingTorus_gaussianDominated beta hbeta.le) chi hdisp

end StatMech.FrontierA
