/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusDissemination.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusReflection.Part10
import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusCharacter.Part3
import Def.StatisticalMechanics.Code.FrontierA.IsingTorusDissemination.Part7
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising

variable {d k : Nat}


theorem isingTorusDisseminatedBox_one
    (h : IsingDyadicTorus d k → Real) :
    IsingTorusDisseminatedBox (fun _ : Fin d => 1) h := by
  intro x hx
  have hx0 : x = 0 := by
    funext i
    apply (ZMod.val_eq_zero (x i)).mp
    have hi : (x i).val < 1 := by simpa using hx i
    omega
  rw [hx0]


theorem isingTorusDisseminatedBox_double
    (sizes : Fin d → Nat) (i : Fin d) (s : Nat)
    (hspos : 0 < s) (hs : s ≤ 2 ^ (k + 1))
    (h : IsingDyadicTorus d k → Real)
    (hbox : IsingTorusDisseminatedBox (Function.update sizes i s) h) :
    IsingTorusDisseminatedBox (Function.update sizes i (2 * s))
      (isingTorusPolarizeLowerAt i (isingTorusBlockShift i s) h) := by
  intro x hx
  have hzeroVal : ((0 : IsingDyadicTorus d k) i).val < s := by
    simpa using hspos
  rw [isingTorusPolarizeLowerAt_eq_of_block_lt i s hs h 0 hzeroVal]
  by_cases hxi : (x i).val < s
  · rw [isingTorusPolarizeLowerAt_eq_of_block_lt i s hs h x hxi]
    apply hbox x
    intro j
    by_cases hji : j = i
    · subst j
      simpa using hxi
    · simpa [hji] using hx j
  · have hxis : s ≤ (x i).val := by omega
    have hxi2 : (x i).val < 2 * s := by
      simpa using hx i
    let y := Function.update x i
      ((2 * s - 1 - (x i).val : Nat) : ZMod (2 ^ (k + 2)))
    have hylt : (y i).val < s := by
      have hnlt : 2 * s - 1 - (x i).val < 2 ^ (k + 2) := by
        have hsmall := isingTorus_block_reflected_val_lt
          s hspos (x i).val hxis hxi2
        have hside : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) :=
          isingTorus_side_eq_two_mul_half'
        omega
      simp [y, ZMod.val_natCast_of_lt hnlt,
        isingTorus_block_reflected_val_lt s hspos (x i).val hxis hxi2]
    rw [isingTorusPolarizeLowerAt_eq_of_mem_second
      i s hspos hs h x hxis hxi2]
    apply hbox y
    intro j
    by_cases hji : j = i
    · subst j
      simpa using hylt
    · simpa [y, hji] using hx j

theorem isingTorus_indexed_max_box_double
    (beta : Real) (hbeta : 0 ≤ beta)
    (h : IsingDyadicTorus d k → Real)
    (gmax g : IsingDyadicTorus d k → IsingDyadicTorus d k)
    (hmax : ∀ g' : IsingDyadicTorus d k → IsingDyadicTorus d k,
      isingTorusShiftedPartition beta (isingTorusIndexedField h g') ≤
        isingTorusShiftedPartition beta (isingTorusIndexedField h gmax))
    (hg : isingTorusShiftedPartition beta (isingTorusIndexedField h g) =
      isingTorusShiftedPartition beta (isingTorusIndexedField h gmax))
    (sizes : Fin d → Nat) (i : Fin d) (s : Nat)
    (hspos : 0 < s) (hs : s ≤ 2 ^ (k + 1))
    (hbox : IsingTorusDisseminatedBox (Function.update sizes i s)
      (isingTorusIndexedField h g)) :
    ∃ g' : IsingDyadicTorus d k → IsingDyadicTorus d k,
      isingTorusShiftedPartition beta (isingTorusIndexedField h g') =
          isingTorusShiftedPartition beta (isingTorusIndexedField h gmax) ∧
        IsingTorusDisseminatedBox (Function.update sizes i (2 * s))
          (isingTorusIndexedField h g') := by
  let a := isingTorusBlockShift (k := k) i s
  let g' := isingTorusPolarizeLowerIndexAt i a g
  have hgmax : ∀ q : IsingDyadicTorus d k → IsingDyadicTorus d k,
      isingTorusShiftedPartition beta (isingTorusIndexedField h q) ≤
        isingTorusShiftedPartition beta (isingTorusIndexedField h g) := by
    intro q
    rw [hg]
    exact hmax q
  have hpres := isingTorus_polarizeLower_preserves_indexed_max
    i a beta hbeta h g hgmax
  refine ⟨g', ?_, ?_⟩
  · simpa [g'] using hpres.trans hg
  · simpa [g', isingTorusIndexedField_polarizeLowerIndexAt] using
      (isingTorusDisseminatedBox_double sizes i s hspos hs
        (isingTorusIndexedField h g) hbox)

theorem isingTorus_indexed_max_disseminate_coordinate
    (beta : Real) (hbeta : 0 ≤ beta)
    (h : IsingDyadicTorus d k → Real)
    (gmax g : IsingDyadicTorus d k → IsingDyadicTorus d k)
    (hmax : ∀ g' : IsingDyadicTorus d k → IsingDyadicTorus d k,
      isingTorusShiftedPartition beta (isingTorusIndexedField h g') ≤
        isingTorusShiftedPartition beta (isingTorusIndexedField h gmax))
    (hg : isingTorusShiftedPartition beta (isingTorusIndexedField h g) =
      isingTorusShiftedPartition beta (isingTorusIndexedField h gmax))
    (sizes : Fin d → Nat) (i : Fin d)
    (hbox : IsingTorusDisseminatedBox (Function.update sizes i 1)
      (isingTorusIndexedField h g)) :
    ∀ r, r ≤ k + 2 →
      ∃ g' : IsingDyadicTorus d k → IsingDyadicTorus d k,
        isingTorusShiftedPartition beta (isingTorusIndexedField h g') =
            isingTorusShiftedPartition beta (isingTorusIndexedField h gmax) ∧
          IsingTorusDisseminatedBox (Function.update sizes i (2 ^ r))
            (isingTorusIndexedField h g') := by
  intro r hr
  induction r with
  | zero =>
      refine ⟨g, hg, ?_⟩
      simpa using hbox
  | succ r ihr =>
      have hrle : r ≤ k + 1 := by omega
      obtain ⟨q, hq, hqbox⟩ := ihr (by omega)
      have hpow : 2 ^ r ≤ 2 ^ (k + 1) :=
        Nat.pow_le_pow_right (by omega) hrle
      obtain ⟨q', hq', hq'box⟩ := isingTorus_indexed_max_box_double
        beta hbeta h gmax q hmax hq sizes i (2 ^ r)
          (pow_pos (by omega) r) hpow hqbox
      refine ⟨q', hq', ?_⟩
      simpa [pow_succ, mul_comm] using hq'box


end StatMech.FrontierA
