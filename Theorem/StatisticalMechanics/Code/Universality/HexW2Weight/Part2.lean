/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW2Weight.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Universality.HexW2Cut.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexInfraWinding
import Def.StatisticalMechanics.Code.Universality.HexW2Weight.Part2


namespace StatMech.Universality

open HexWalk List

open scoped BigOperators


@[simp] theorem hexW2_split_fst_wt (a : ℂ) (h0 : ℤ) (x : ℝ) (memD : List ℤ → Prop)
    (d : {ts // memD ts}) :
    hexW2_halfWt x (hexW2_split a h0 memD d).1
      = hexSAWwt a h0 x (d.1.take (hexW2_cutPos h0 d.1)) :=
  rfl


@[simp] theorem hexW2_split_snd_wt (a : ℂ) (h0 : ℤ) (x : ℝ) (memD : List ℤ → Prop)
    (d : {ts // memD ts}) :
    hexW2_halfWt x (hexW2_split a h0 memD d).2
      = hexSAWwt (hexDropMid a h0 d.1 (hexW2_cutPos h0 d.1))
          (h0 + (d.1.take (hexW2_cutPos h0 d.1)).sum) x (d.1.drop (hexW2_cutPos h0 d.1)) :=
  rfl


theorem hexW2_split_injective (a : ℂ) (h0 : ℤ) (memD : List ℤ → Prop) :
    Function.Injective (hexW2_split a h0 memD) := by
  intro d d' heq
  
  have hfst : (hexW2_split a h0 memD d).1 = (hexW2_split a h0 memD d').1 :=
    congrArg Prod.fst heq
  have hsnd : (hexW2_split a h0 memD d).2 = (hexW2_split a h0 memD d').2 :=
    congrArg Prod.snd heq
  have htake : d.1.take (hexW2_cutPos h0 d.1) = d'.1.take (hexW2_cutPos h0 d'.1) :=
    congrArg HexW2Half.turns hfst
  have hdrop : d.1.drop (hexW2_cutPos h0 d.1) = d'.1.drop (hexW2_cutPos h0 d'.1) :=
    congrArg HexW2Half.turns hsnd
  
  apply Subtype.ext
  calc d.1 = d.1.take (hexW2_cutPos h0 d.1) ++ d.1.drop (hexW2_cutPos h0 d.1) :=
        (List.take_append_drop _ _).symm
    _ = d'.1.take (hexW2_cutPos h0 d'.1) ++ d'.1.drop (hexW2_cutPos h0 d'.1) := by
        rw [htake, hdrop]
    _ = d'.1 := List.take_append_drop _ _


end StatMech.Universality
