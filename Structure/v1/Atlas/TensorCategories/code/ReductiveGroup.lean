

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ReductiveGroup.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-- Combinatorial data abstracting a reductive group `G` acting on a
representation `V`, together with a unipotent subgroup `U`, an indexing `I` of
irreducible subrepresentations `W i`, and bookkeeping axioms: faithfulness of `U`,
irreducibility of each `W i`, complete reducibility of `V`, the existence of
unipotent fixed points in any nonzero subrepresentation, and the existence of the
fixed-point subspace under `U` of any subrepresentation. -/
structure ReductiveGroupData where
  G : Type
  U : Type
  V : Type
  g_one : G
  u_incl : U → G
  u_one : U
  u_incl_one : u_incl u_one = g_one
  act : G → V → V
  v_zero : V
  act_zero : ∀ g : G, act g v_zero = v_zero
  act_id : ∀ v : V, act g_one v = v
  u_faithful : ∀ u : U, (∀ v : V, act (u_incl u) v = v) → u = u_one
  Sub : Type
  mem_sub : Sub → V → Prop
  I : Type
  W : I → Sub
  W_nonempty : ∀ i : I, ∃ w : V, mem_sub (W i) w ∧ w ≠ v_zero
  irred : ∀ i : I, ∀ W' : Sub,
    (∀ w : V, mem_sub W' w → mem_sub (W i) w) →
    (∃ w : V, mem_sub W' w ∧ w ≠ v_zero) →
    (∀ w : V, mem_sub (W i) w → mem_sub W' w)
  completely_reducible :
    ∀ g : G, (∀ i : I, ∀ w : V, mem_sub (W i) w → act g w = w) → ∀ v : V, act g v = v
  unipotent_fixed_pt :
    ∀ W' : Sub, (∃ w : V, mem_sub W' w ∧ w ≠ v_zero) →
      ∃ w : V, mem_sub W' w ∧ w ≠ v_zero ∧ (∀ u : U, act (u_incl u) w = w)
  fixed_pts_sub :
    ∀ W' : Sub, ∃ W_U : Sub,
      (∀ w : V, mem_sub W_U w ↔ (mem_sub W' w ∧ ∀ u : U, act (u_incl u) w = w))

