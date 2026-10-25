/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexHalfEdgeClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexW2Weight.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexPerScaleBijClose.Part4
import Structure.StatisticalMechanics.Code.Universality.HexHalfEdgeClose


namespace StatMech.Universality

open HexWalk List

open scoped BigOperators


noncomputable def hhe_halfClass (a : ℂ) (h0 : ℤ) (x : ℝ) (memD memB : List ℤ → Prop)
    (htake : ∀ d : {ts // memD ts}, memB (d.1.take (hexW2_cutPos h0 d.1)))
    (hdrop : ∀ d : {ts // memD ts}, memB (d.1.drop (hexW2_cutPos h0 d.1))) :
    HexHalfClass a h0 x memD memB where
  lower := fun d => ⟨d.1.take (hexW2_cutPos h0 d.1), htake d⟩
  upper := fun d => ⟨d.1.drop (hexW2_cutPos h0 d.1), hdrop d⟩
  hlow := fun d => rfl
  hupp := fun d => by
    change hexSAWwt a h0 x (d.1.drop (hexW2_cutPos h0 d.1))
      = hexSAWwt (hexDropMid a h0 d.1 (hexW2_cutPos h0 d.1))
          (h0 + (d.1.take (hexW2_cutPos h0 d.1)).sum) x (d.1.drop (hexW2_cutPos h0 d.1))
    exact (hhe_hexSAWwt_rebase a (hexDropMid a h0 d.1 (hexW2_cutPos h0 d.1))
      h0 (h0 + (d.1.take (hexW2_cutPos h0 d.1)).sum) x (d.1.drop (hexW2_cutPos h0 d.1))).symm
  pair_inj := by
    intro d d' heq
    have h1 := congrArg Prod.fst heq
    have h2 := congrArg Prod.snd heq
    have htk : d.1.take (hexW2_cutPos h0 d.1) = d'.1.take (hexW2_cutPos h0 d'.1) :=
      congrArg Subtype.val h1
    have hdp : d.1.drop (hexW2_cutPos h0 d.1) = d'.1.drop (hexW2_cutPos h0 d'.1) :=
      congrArg Subtype.val h2
    apply Subtype.ext
    calc d.1 = d.1.take (hexW2_cutPos h0 d.1) ++ d.1.drop (hexW2_cutPos h0 d.1) :=
          (List.take_append_drop _ _).symm
      _ = d'.1.take (hexW2_cutPos h0 d'.1) ++ d'.1.drop (hexW2_cutPos h0 d'.1) := by
          rw [htk, hdp]
      _ = d'.1 := List.take_append_drop _ _


noncomputable def hhe_halfClass_of_halves (a : ℂ) (h0 : ℤ) (x : ℝ)
    (memD memB : List ℤ → Prop) (HIC : HexHalvesInColumn h0 memD memB) :
    HexHalfClass a h0 x memD memB :=
  hhe_halfClass a h0 x memD memB HIC.htake HIC.hdrop


end StatMech.Universality
