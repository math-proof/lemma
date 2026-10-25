import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexConcreteRegion.Part5
open StatMech StatMech.Universality


/--
[hexConcrete_halfStep_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConcreteRegion.lean)
-/
@[path]
private lemma hexConcrete_halfStep_sub_eq
-- given
  (h : ℤ) :
-- imply
  halfStep (h - 1) = -(hexOmega * halfStep h) := by
-- proof
  apply StatMech.Universality.hexConcrete_halfStep_sub h

/--
[hexConcrete_halfStep_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConcreteRegion.lean)
-/
@[path]
private lemma hexConcrete_halfStep_add_eq
-- given
  (h : ℤ) :
-- imply
  halfStep (h + 1) = -(hexOmega ^ 2 * halfStep h) := by
-- proof
  apply StatMech.Universality.hexConcrete_halfStep_add h

/--
[hexConcrete_halfStep_sub2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConcreteRegion.lean)
-/
@[path]
private lemma hexConcrete_halfStep_sub2_eq
-- given
  (h : ℤ) :
-- imply
  halfStep (h - 2) = hexOmega ^ 2 * halfStep h := by
-- proof
  apply StatMech.Universality.hexConcrete_halfStep_sub2 h

/--
[hexConcrete_halfStep_add2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConcreteRegion.lean)
-/
@[path]
private lemma hexConcrete_halfStep_add2_eq
-- given
  (h : ℤ) :
-- imply
  halfStep (h + 2) = hexOmega * halfStep h := by
-- proof
  apply StatMech.Universality.hexConcrete_halfStep_add2 h

/--
[hexConcrete_halfStep_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConcreteRegion.lean)
-/
@[path]
private lemma hexConcrete_halfStep_ne_eq
-- given
  (h : ℤ) :
-- imply
  halfStep h ≠ 0 := by
-- proof
  apply StatMech.Universality.hexConcrete_halfStep_ne h

/--
[hexConcrete_du_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConcreteRegion.lean)
-/
@[path]
private lemma hexConcrete_du_ne_eq
-- given
  (h0 : ℤ) :
-- imply
  (-halfStep h0) ≠ 0 := by
-- proof
  apply StatMech.Universality.hexConcrete_du_ne h0

/--
[hexConcrete_omega_cubic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConcreteRegion.lean)
-/
@[path]
private lemma hexConcrete_omega_cubic_eq :
-- imply
  hexOmega ^ 2 = -hexOmega - 1 := by
-- proof
  apply StatMech.Universality.hexConcrete_omega_cubic

/--
[hexConcrete_omega_im_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConcreteRegion.lean)
-/
@[path]
private lemma hexConcrete_omega_im_pos_eq :
-- imply
  0 < hexOmega.im := by
-- proof
  apply StatMech.Universality.hexConcrete_omega_im_pos

/--
[hexConcrete_omega_lin_indep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConcreteRegion.lean)
-/
@[path]
private lemma hexConcrete_omega_lin_indep_eq
  {α β : ℝ}
-- given
  (h : (α : ℂ) + (β : ℂ) * hexOmega = 0) :
-- imply
  α = 0 ∧ β = 0 := by
-- proof
  apply StatMech.Universality.hexConcrete_omega_lin_indep α β h

/--
[hexConcrete_mid_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConcreteRegion.lean)
-/
@[path]
private lemma hexConcrete_mid_ne_eq
  {a s : ℂ}
  {α₁ β₁ α₂ β₂ : ℝ}
-- given
  (hs : s ≠ 0)
  (hne : ¬(α₁ = α₂ ∧ β₁ = β₂)) :
-- imply
  a + ((α₁ : ℂ) + (β₁ : ℂ) * hexOmega) * s ≠ a + ((α₂ : ℂ) + (β₂ : ℂ) * hexOmega) * s := by
-- proof
  apply StatMech.Universality.hexConcrete_mid_ne a s hs α₁ β₁ α₂ β₂ hne

/--
[hexConcrete_mids_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConcreteRegion.lean)
-/
@[path]
private lemma hexConcrete_mids_one_eq
  {a : ℂ}
-- given
  (h t : ℤ) :
-- imply
  (ofTurns a h [t]).mids = [a, a + halfStep h + halfStep (h + t)] := by
-- proof
  apply StatMech.Universality.hexConcrete_mids_one a h t

/--
[hexConcrete_endMid_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConcreteRegion.lean)
-/
@[path]
private lemma hexConcrete_endMid_one_eq
  {a : ℂ}
-- given
  (h t : ℤ) :
-- imply
  (ofTurns a h [t]).endMid = a + halfStep h + halfStep (h + t) := by
-- proof
  apply StatMech.Universality.hexConcrete_endMid_one a h t

/--
[hexConcrete_vertices_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConcreteRegion.lean)
-/
@[path]
private lemma hexConcrete_vertices_one_eq
  {a : ℂ}
-- given
  (h t : ℤ) :
-- imply
  (ofTurns a h [t]).vertices = [a + halfStep h, a + halfStep h + halfStep (h + t) + halfStep (h + t)] := by
-- proof
  apply StatMech.Universality.hexConcrete_vertices_one a h t

/--
[hexConcrete_endMid_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConcreteRegion.lean)
-/
@[path]
private lemma hexConcrete_endMid_two_eq
  {a : ℂ}
-- given
  (h t1 t2 : ℤ) :
-- imply
  (ofTurns a h [t1, t2]).endMid = a + halfStep h + halfStep (h + t1) + halfStep (h + t1) + halfStep (h + t1 + t2) := by
-- proof
  apply StatMech.Universality.hexConcrete_endMid_two a h t1 t2

/--
[hexConcrete_saw_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConcreteRegion.lean)
-/
@[path]
private lemma hexConcrete_saw_one_eq
  {a : ℂ}
-- given
  (h t : ℤ) :
-- imply
  (ofTurns a h [t]).IsSAW := by
-- proof
  apply StatMech.Universality.hexConcrete_saw_one a h t

/--
[hexConcrete_legalSAW_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConcreteRegion.lean)
-/
@[path]
private lemma hexConcrete_legalSAW_one_eq
  {a : ℂ}
-- given
  (h t : ℤ)
  (ht : t = 1 ∨ t = -1) :
-- imply
  (ofTurns a h [t]).IsLegalSAW := by
-- proof
  apply StatMech.Universality.hexConcrete_legalSAW_one a h t ht

/--
[hexConcreteDu_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConcreteRegion.lean)
-/
@[path]
private lemma hexConcreteDu_ne_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  hexConcreteDu a h0 ≠ 0 := by
-- proof
  apply StatMech.Universality.hexConcreteDu_ne a h0

/--
[hexConcrete_p_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConcreteRegion.lean)
-/
@[path]
private lemma hexConcrete_p_eq_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  hexConcreteV a h0 + hexConcreteDu a h0 = a := by
-- proof
  apply StatMech.Universality.hexConcrete_p_eq a h0

/--
[hexConcrete_endsAt_p](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConcreteRegion.lean)
-/
@[path]
private lemma hexConcrete_endsAt_p_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  (ofTurns a h0 []).EndsAt (hexConcreteV a h0 + hexConcreteDu a h0) := by
-- proof
  apply StatMech.Universality.hexConcrete_endsAt_p a h0

/--
[hexConcrete_endsAt_q](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConcreteRegion.lean)
-/
@[path]
private lemma hexConcrete_endsAt_q_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  (ofTurns a h0 [-1]).EndsAt (hexConcreteQ a h0) := by
-- proof
  apply StatMech.Universality.hexConcrete_endsAt_q a h0

/--
[hexConcrete_endsAt_r](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConcreteRegion.lean)
-/
@[path]
private lemma hexConcrete_endsAt_r_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  (ofTurns a h0 [1]).EndsAt (hexConcreteR a h0) := by
-- proof
  apply StatMech.Universality.hexConcrete_endsAt_r a h0

/--
[hexConcrete_a_ne_q](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConcreteRegion.lean)
-/
@[path]
private lemma hexConcrete_a_ne_q_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  a ≠ hexConcreteQ a h0 := by
-- proof
  apply StatMech.Universality.hexConcrete_a_ne_q a h0

/--
[hexConcrete_a_ne_r](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConcreteRegion.lean)
-/
@[path]
private lemma hexConcrete_a_ne_r_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  a ≠ hexConcreteR a h0 := by
-- proof
  apply StatMech.Universality.hexConcrete_a_ne_r a h0

/--
[hexConcrete_q_ne_r](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConcreteRegion.lean)
-/
@[path]
private lemma hexConcrete_q_ne_r_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  hexConcreteQ a h0 ≠ hexConcreteR a h0 := by
-- proof
  apply StatMech.Universality.hexConcrete_q_ne_r a h0

/--
[hexConcrete_mids_qext](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConcreteRegion.lean)
-/
@[path]
private lemma hexConcrete_mids_qext_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  (ofTurns a h0 [-1]).mids = [a, hexConcreteQ a h0] := by
-- proof
  apply StatMech.Universality.hexConcrete_mids_qext a h0

/--
[hexConcrete_mids_rext](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConcreteRegion.lean)
-/
@[path]
private lemma hexConcrete_mids_rext_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  (ofTurns a h0 [1]).mids = [a, hexConcreteR a h0] := by
-- proof
  apply StatMech.Universality.hexConcrete_mids_rext a h0

/--
[hexConcrete_qext_not_passes_r](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConcreteRegion.lean)
-/
@[path]
private lemma hexConcrete_qext_not_passes_r_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  ¬ PassesThrough a h0 [-1] (hexConcreteR a h0) := by
-- proof
  apply StatMech.Universality.hexConcrete_qext_not_passes_r a h0

/--
[hexConcrete_rext_not_passes_q](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConcreteRegion.lean)
-/
@[path]
private lemma hexConcrete_rext_not_passes_q_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  ¬ PassesThrough a h0 [1] (hexConcreteQ a h0) := by
-- proof
  apply StatMech.Universality.hexConcrete_rext_not_passes_q a h0

/--
[hexConcrete_atoms](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConcreteRegion.lean)
-/
@[path]
private lemma hexConcrete_atoms_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  ((ofTurns a h0 []).IsLegalSAW ∧ (ofTurns a h0 []).EndsAt (hexConcreteV a h0 + hexConcreteDu a h0)) ∧ ((ofTurns a h0 [-1]).IsLegalSAW ∧ (ofTurns a h0 [-1]).EndsAt (hexConcreteV a h0 + hexOmega * hexConcreteDu a h0)) ∧ ((ofTurns a h0 [1]).IsLegalSAW ∧ (ofTurns a h0 [1]).EndsAt (hexConcreteV a h0 + hexOmega ^ 2 * hexConcreteDu a h0)) ∧ (¬ PassesThrough a h0 [-1] (hexConcreteV a h0 + hexOmega ^ 2 * hexConcreteDu a h0)) ∧ (¬ PassesThrough a h0 [1] (hexConcreteV a h0 + hexOmega * hexConcreteDu a h0)) := by
-- proof
  apply StatMech.Universality.hexConcrete_atoms a h0

/--
[hexConcrete_q_canon](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConcreteRegion.lean)
-/
@[path]
private lemma hexConcrete_q_canon_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  hexConcreteQ a h0 = a + (((1 : ℝ) : ℂ) + ((-1 : ℝ) : ℂ) * hexOmega) * halfStep h0 := by
-- proof
  apply StatMech.Universality.hexConcrete_q_canon a h0

/--
[hexConcrete_r_canon](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConcreteRegion.lean)
-/
@[path]
private lemma hexConcrete_r_canon_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  hexConcreteR a h0 = a + (((2 : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * hexOmega) * halfStep h0 := by
-- proof
  apply StatMech.Universality.hexConcrete_r_canon a h0

/--
[hexConcrete_endMid_mm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConcreteRegion.lean)
-/
@[path]
private lemma hexConcrete_endMid_mm_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  (ofTurns a h0 [-1, -1]).endMid = a + (((0 : ℝ) : ℂ) + ((-3 : ℝ) : ℂ) * hexOmega) * halfStep h0 := by
-- proof
  apply StatMech.Universality.hexConcrete_endMid_mm a h0

/--
[hexConcrete_endMid_mp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConcreteRegion.lean)
-/
@[path]
private lemma hexConcrete_endMid_mp_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  (ofTurns a h0 [-1, 1]).endMid = a + (((2 : ℝ) : ℂ) + ((-2 : ℝ) : ℂ) * hexOmega) * halfStep h0 := by
-- proof
  apply StatMech.Universality.hexConcrete_endMid_mp a h0

/--
[hexConcrete_endMid_pm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConcreteRegion.lean)
-/
@[path]
private lemma hexConcrete_endMid_pm_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  (ofTurns a h0 [1, -1]).endMid = a + (((4 : ℝ) : ℂ) + ((2 : ℝ) : ℂ) * hexOmega) * halfStep h0 := by
-- proof
  apply StatMech.Universality.hexConcrete_endMid_pm a h0

/--
[hexConcrete_endMid_pp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConcreteRegion.lean)
-/
@[path]
private lemma hexConcrete_endMid_pp_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  (ofTurns a h0 [1, 1]).endMid = a + (((3 : ℝ) : ℂ) + ((3 : ℝ) : ℂ) * hexOmega) * halfStep h0 := by
-- proof
  apply StatMech.Universality.hexConcrete_endMid_pp a h0

/--
[hexConcrete_len2_endMid_not_mid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConcreteRegion.lean)
-/
@[path]
private lemma hexConcrete_len2_endMid_not_mid_eq
  {a : ℂ}
  {t1 t2 : ℤ}
-- given
  (h0 : ℤ)
  (h1 : t1 = 1 ∨ t1 = -1)
  (h2 : t2 = 1 ∨ t2 = -1) :
-- imply
  (ofTurns a h0 [t1, t2]).endMid ≠ a ∧ (ofTurns a h0 [t1, t2]).endMid ≠ hexConcreteQ a h0 ∧ (ofTurns a h0 [t1, t2]).endMid ≠ hexConcreteR a h0 := by
-- proof
  apply StatMech.Universality.hexConcrete_len2_endMid_not_mid a h0 t1 t2 h1 h2

/--
[hexConcrete_v0_canon](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConcreteRegion.lean)
-/
@[path]
private lemma hexConcrete_v0_canon_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  hexConcreteV0 a h0 = a + (((1 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * hexOmega) * halfStep h0 := by
-- proof
  apply StatMech.Universality.hexConcrete_v0_canon a h0

/--
[hexConcrete_vq_canon](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConcreteRegion.lean)
-/
@[path]
private lemma hexConcrete_vq_canon_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  hexConcreteVq a h0 = a + (((1 : ℝ) : ℂ) + ((-2 : ℝ) : ℂ) * hexOmega) * halfStep h0 := by
-- proof
  apply StatMech.Universality.hexConcrete_vq_canon a h0

/--
[hexConcrete_vr_canon](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConcreteRegion.lean)
-/
@[path]
private lemma hexConcrete_vr_canon_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  hexConcreteVr a h0 = a + (((3 : ℝ) : ℂ) + ((2 : ℝ) : ℂ) * hexOmega) * halfStep h0 := by
-- proof
  apply StatMech.Universality.hexConcrete_vr_canon a h0

/--
[hexConcrete_verts_distinct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConcreteRegion.lean)
-/
@[path]
private lemma hexConcrete_verts_distinct_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  hexConcreteV0 a h0 ≠ hexConcreteVq a h0 ∧ hexConcreteV0 a h0 ≠ hexConcreteVr a h0 ∧ hexConcreteVq a h0 ≠ hexConcreteVr a h0 := by
-- proof
  apply StatMech.Universality.hexConcrete_verts_distinct a h0

/--
[hexConcrete_verts_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConcreteRegion.lean)
-/
@[path]
private lemma hexConcrete_verts_card_eq
  {a : ℂ}
-- given
  (h0 : ℤ)
  (hclosure : ∀ W : HexWalk, (∀ m ∈ W.mids, m ∈ ({a, hexConcreteQ a h0, hexConcreteR a h0} : Finset ℂ)) → ∀ x ∈ W.vertices, x ∈ ({hexConcreteV0 a h0, hexConcreteVq a h0, hexConcreteVr a h0} : Finset ℂ)) :
-- imply
  (hexConcrete_region a h0 hclosure).verts.card = 3 := by
-- proof
  apply StatMech.Universality.hexConcrete_verts_card a h0 hclosure

/--
[hexConcrete_inRegion_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConcreteRegion.lean)
-/
@[path]
private lemma hexConcrete_inRegion_iff_eq
  {a : ℂ}
  {z : ℂ}
-- given
  (h0 : ℤ)
  (hclosure : ∀ W : HexWalk, (∀ m ∈ W.mids, m ∈ ({a, hexConcreteQ a h0, hexConcreteR a h0} : Finset ℂ)) → ∀ x ∈ W.vertices, x ∈ ({hexConcreteV0 a h0, hexConcreteVq a h0, hexConcreteVr a h0} : Finset ℂ)) :
-- imply
  (hexConcrete_region a h0 hclosure).inRegion z ↔ (z = a ∨ z = hexConcreteQ a h0 ∨ z = hexConcreteR a h0) := by
-- proof
  apply StatMech.Universality.hexConcrete_inRegion_iff a h0 hclosure z

/--
[hexConcrete_staysIn_p](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConcreteRegion.lean)
-/
@[path]
private lemma hexConcrete_staysIn_p_eq
  {a : ℂ}
-- given
  (h0 : ℤ)
  (hclosure : ∀ W : HexWalk, (∀ m ∈ W.mids, m ∈ ({a, hexConcreteQ a h0, hexConcreteR a h0} : Finset ℂ)) → ∀ x ∈ W.vertices, x ∈ ({hexConcreteV0 a h0, hexConcreteVq a h0, hexConcreteVr a h0} : Finset ℂ)) :
-- imply
  (ofTurns a h0 []).StaysIn (hexConcrete_region a h0 hclosure).inRegion := by
-- proof
  apply StatMech.Universality.hexConcrete_staysIn_p a h0 hclosure

/--
[hexConcrete_staysIn_q](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConcreteRegion.lean)
-/
@[path]
private lemma hexConcrete_staysIn_q_eq
  {a : ℂ}
-- given
  (h0 : ℤ)
  (hclosure : ∀ W : HexWalk, (∀ m ∈ W.mids, m ∈ ({a, hexConcreteQ a h0, hexConcreteR a h0} : Finset ℂ)) → ∀ x ∈ W.vertices, x ∈ ({hexConcreteV0 a h0, hexConcreteVq a h0, hexConcreteVr a h0} : Finset ℂ)) :
-- imply
  (ofTurns a h0 [-1]).StaysIn (hexConcrete_region a h0 hclosure).inRegion := by
-- proof
  apply StatMech.Universality.hexConcrete_staysIn_q a h0 hclosure

/--
[hexConcrete_staysIn_r](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConcreteRegion.lean)
-/
@[path]
private lemma hexConcrete_staysIn_r_eq
  {a : ℂ}
-- given
  (h0 : ℤ)
  (hclosure : ∀ W : HexWalk, (∀ m ∈ W.mids, m ∈ ({a, hexConcreteQ a h0, hexConcreteR a h0} : Finset ℂ)) → ∀ x ∈ W.vertices, x ∈ ({hexConcreteV0 a h0, hexConcreteVq a h0, hexConcreteVr a h0} : Finset ℂ)) :
-- imply
  (ofTurns a h0 [1]).StaysIn (hexConcrete_region a h0 hclosure).inRegion := by
-- proof
  apply StatMech.Universality.hexConcrete_staysIn_r a h0 hclosure

/--
[hexConcrete_support_classify](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConcreteRegion.lean)
-/
@[path]
private lemma hexConcrete_support_classify_eq
  {a : ℂ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hclosure : ∀ W : HexWalk, (∀ m ∈ W.mids, m ∈ ({a, hexConcreteQ a h0, hexConcreteR a h0} : Finset ℂ)) → ∀ x ∈ W.vertices, x ∈ ({hexConcreteV0 a h0, hexConcreteVq a h0, hexConcreteVr a h0} : Finset ℂ))
  (hlegal : (ofTurns a h0 ts).IsLegalSAW)
  (hstay : (ofTurns a h0 ts).StaysIn (hexConcrete_region a h0 hclosure).inRegion) :
-- imply
  ts = [] ∨ ts = [-1] ∨ ts = [1] := by
-- proof
  apply StatMech.Universality.hexConcrete_support_classify a h0 hclosure ts hlegal hstay

/--
[hexConcrete_covering_p](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConcreteRegion.lean)
-/
@[path]
private lemma hexConcrete_covering_p_eq
  {a : ℂ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hclosure : ∀ W : HexWalk, (∀ m ∈ W.mids, m ∈ ({a, hexConcreteQ a h0, hexConcreteR a h0} : Finset ℂ)) → ∀ x ∈ W.vertices, x ∈ ({hexConcreteV0 a h0, hexConcreteVq a h0, hexConcreteVr a h0} : Finset ℂ))
  (hsupp : ts ∈ Function.support (combinedSummand (hexConcrete_region a h0 hclosure).inRegion a h0 (hexConcreteV a h0) (hexConcreteDu a h0)))
  (hp : (ofTurns a h0 ts).EndsAt (hexConcreteV a h0 + hexConcreteDu a h0)) :
-- imply
  ts = [] := by
-- proof
  apply StatMech.Universality.hexConcrete_covering_p a h0 hclosure ts hsupp hp

/--
[hexConcrete_covering_q](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConcreteRegion.lean)
-/
@[path]
private lemma hexConcrete_covering_q_eq
  {a : ℂ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hclosure : ∀ W : HexWalk, (∀ m ∈ W.mids, m ∈ ({a, hexConcreteQ a h0, hexConcreteR a h0} : Finset ℂ)) → ∀ x ∈ W.vertices, x ∈ ({hexConcreteV0 a h0, hexConcreteVq a h0, hexConcreteVr a h0} : Finset ℂ))
  (hsupp : ts ∈ Function.support (combinedSummand (hexConcrete_region a h0 hclosure).inRegion a h0 (hexConcreteV a h0) (hexConcreteDu a h0)))
  (hq : (ofTurns a h0 ts).EndsAt (hexConcreteV a h0 + hexOmega * hexConcreteDu a h0)) :
-- imply
  ts = [-1] := by
-- proof
  apply StatMech.Universality.hexConcrete_covering_q a h0 hclosure ts hsupp hq

/--
[hexConcrete_covering_r](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConcreteRegion.lean)
-/
@[path]
private lemma hexConcrete_covering_r_eq
  {a : ℂ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hclosure : ∀ W : HexWalk, (∀ m ∈ W.mids, m ∈ ({a, hexConcreteQ a h0, hexConcreteR a h0} : Finset ℂ)) → ∀ x ∈ W.vertices, x ∈ ({hexConcreteV0 a h0, hexConcreteVq a h0, hexConcreteVr a h0} : Finset ℂ))
  (hsupp : ts ∈ Function.support (combinedSummand (hexConcrete_region a h0 hclosure).inRegion a h0 (hexConcreteV a h0) (hexConcreteDu a h0)))
  (hr : (ofTurns a h0 ts).EndsAt (hexConcreteV a h0 + hexOmega ^ 2 * hexConcreteDu a h0)) :
-- imply
  ts = [1] := by
-- proof
  apply StatMech.Universality.hexConcrete_covering_r a h0 hclosure ts hsupp hr

/--
[hexConcrete_obs_p](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConcreteRegion.lean)
-/
@[path]
private lemma hexConcrete_obs_p_eq
  {a : ℂ}
-- given
  (h0 : ℤ)
  (hclosure : ∀ W : HexWalk, (∀ m ∈ W.mids, m ∈ ({a, hexConcreteQ a h0, hexConcreteR a h0} : Finset ℂ)) → ∀ x ∈ W.vertices, x ∈ ({hexConcreteV0 a h0, hexConcreteVq a h0, hexConcreteVr a h0} : Finset ℂ)) :
-- imply
  parafObservable (hexConcrete_region a h0 hclosure).inRegion a h0 (hexConcreteV a h0 + hexConcreteDu a h0) (5/8) hexChi = parafSummand (hexConcrete_region a h0 hclosure).inRegion a h0 (hexConcreteV a h0 + hexConcreteDu a h0) (5/8) hexChi [] := by
-- proof
  apply StatMech.Universality.hexConcrete_obs_p a h0 hclosure

/--
[hexConcrete_obs_q](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConcreteRegion.lean)
-/
@[path]
private lemma hexConcrete_obs_q_eq
  {a : ℂ}
-- given
  (h0 : ℤ)
  (hclosure : ∀ W : HexWalk, (∀ m ∈ W.mids, m ∈ ({a, hexConcreteQ a h0, hexConcreteR a h0} : Finset ℂ)) → ∀ x ∈ W.vertices, x ∈ ({hexConcreteV0 a h0, hexConcreteVq a h0, hexConcreteVr a h0} : Finset ℂ)) :
-- imply
  parafObservable (hexConcrete_region a h0 hclosure).inRegion a h0 (hexConcreteV a h0 + hexOmega * hexConcreteDu a h0) (5/8) hexChi = parafSummand (hexConcrete_region a h0 hclosure).inRegion a h0 (hexConcreteV a h0 + hexOmega * hexConcreteDu a h0) (5/8) hexChi [-1] := by
-- proof
  apply StatMech.Universality.hexConcrete_obs_q a h0 hclosure

/--
[hexConcrete_obs_r](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConcreteRegion.lean)
-/
@[path]
private lemma hexConcrete_obs_r_eq
  {a : ℂ}
-- given
  (h0 : ℤ)
  (hclosure : ∀ W : HexWalk, (∀ m ∈ W.mids, m ∈ ({a, hexConcreteQ a h0, hexConcreteR a h0} : Finset ℂ)) → ∀ x ∈ W.vertices, x ∈ ({hexConcreteV0 a h0, hexConcreteVq a h0, hexConcreteVr a h0} : Finset ℂ)) :
-- imply
  parafObservable (hexConcrete_region a h0 hclosure).inRegion a h0 (hexConcreteV a h0 + hexOmega ^ 2 * hexConcreteDu a h0) (5/8) hexChi = parafSummand (hexConcrete_region a h0 hclosure).inRegion a h0 (hexConcreteV a h0 + hexOmega ^ 2 * hexConcreteDu a h0) (5/8) hexChi [1] := by
-- proof
  apply StatMech.Universality.hexConcrete_obs_r a h0 hclosure

/--
[hexConcrete_summable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConcreteRegion.lean)
-/
@[path]
private lemma hexConcrete_summable_eq
  {a : ℂ}
  {z : ℂ}
-- given
  (h0 : ℤ)
  (hclosure : ∀ W : HexWalk, (∀ m ∈ W.mids, m ∈ ({a, hexConcreteQ a h0, hexConcreteR a h0} : Finset ℂ)) → ∀ x ∈ W.vertices, x ∈ ({hexConcreteV0 a h0, hexConcreteVq a h0, hexConcreteVr a h0} : Finset ℂ)) :
-- imply
  Summable fun ts => parafSummand (hexConcrete_region a h0 hclosure).inRegion a h0 z (5/8) hexChi ts := by
-- proof
  apply StatMech.Universality.hexConcrete_summable a h0 hclosure z

/--
[hexConcrete_vertex_relation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConcreteRegion.lean)
-/
@[path]
private lemma hexConcrete_vertex_relation_eq
  {a : ℂ}
-- given
  (h0 : ℤ)
  (hclosure : ∀ W : HexWalk, (∀ m ∈ W.mids, m ∈ ({a, hexConcreteQ a h0, hexConcreteR a h0} : Finset ℂ)) → ∀ x ∈ W.vertices, x ∈ ({hexConcreteV0 a h0, hexConcreteVq a h0, hexConcreteVr a h0} : Finset ℂ)) :
-- imply
  ((hexConcreteV a h0 + hexConcreteDu a h0) - hexConcreteV a h0) * parafObservable (hexConcrete_region a h0 hclosure).inRegion a h0 (hexConcreteV a h0 + hexConcreteDu a h0) (5/8) hexChi + ((hexConcreteV a h0 + hexOmega * hexConcreteDu a h0) - hexConcreteV a h0) * parafObservable (hexConcrete_region a h0 hclosure).inRegion a h0 (hexConcreteV a h0 + hexOmega * hexConcreteDu a h0) (5/8) hexChi + ((hexConcreteV a h0 + hexOmega ^ 2 * hexConcreteDu a h0) - hexConcreteV a h0) * parafObservable (hexConcrete_region a h0 hclosure).inRegion a h0 (hexConcreteV a h0 + hexOmega ^ 2 * hexConcreteDu a h0) (5/8) hexChi = 0 := by
-- proof
  apply StatMech.Universality.hexConcrete_vertex_relation a h0 hclosure


-- created on 2026-10-23
