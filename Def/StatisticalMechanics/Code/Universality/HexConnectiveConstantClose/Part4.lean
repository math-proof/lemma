/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConnectiveConstantClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryIdentityClose.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeRealizeClose.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexZDivTauClose.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexHammersleyWelshClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.HexConnectiveConstantClose.Part4


namespace StatMech.Universality

open Filter Topology

open scoped Topology Real NNReal BigOperators


noncomputable def hxf_wCut : HexHighestCut hexChiE⁻¹ where
  D := Empty
  B := Unit
  wtγ := Empty.elim
  wtB := fun _ => 1
  wtB_nn := fun _ => zero_le_one
  wtγ_nn := fun d => d.elim
  split := fun d => d.elim
  split_inj := fun d => d.elim
  weight_bound := fun d => d.elim
  D_summable := summable_empty
  B_summable := summable_of_hasFiniteSupport (Set.toFinite _)


noncomputable def hxf_wEB (v : ℕ) : hxf_wCut.B ≃ {i : ℕ // hxf_wEυ.scale i = v + 1} where
  toFun := fun _ => ⟨v + 1, rfl⟩
  invFun := fun _ => ()
  left_inv := fun _ => rfl
  right_inv := fun i => Subtype.ext i.2.symm


noncomputable def hxf_wED (v : ℕ) : hxf_wCut.D ≃ {i : Empty // hxf_wEla.scale i = v + 1} where
  toFun := fun d => d.elim
  invFun := fun i => i.1.elim
  left_inv := fun d => d.elim
  right_inv := fun i => i.1.elim


noncomputable def hxf_wSideEτ : HexContourEmb ℕ ℕ where
  wtSAW := fun n => hxf_wc n * hexChiE ^ n
  emb := id
  emb_inj := Function.injective_id
  wtSAW_nn := hxf_wc_wt_nn


noncomputable def hxf_wSide : HexSideContour ℕ (fun _ => (0:ℝ)) where
  Eτ := hxf_wSideEτ
  posWit := fun ⟨_, _, hpos⟩ => absurd hpos (by norm_num)
  shift := fun i n => i + n
  shift_inj := fun i => add_right_injective i
  shift_wt := fun i n => by
    show hxf_wSideEτ.wtContour (i + n) = hxf_wSideEτ.wtContour i
    unfold HexContourEmb.wtContour
    show hxf_wc (i + n) * hexChiE ^ (i + n) = hxf_wc i * hexChiE ^ i
    rw [hxf_wc_wt, hxf_wc_wt]


end StatMech.Universality
