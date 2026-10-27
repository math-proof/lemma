import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.Buildings.code.GeometricAlgebra.CorBilinearHermitianForms
open Formalization Formalization.GeometricAlgebra
open Garrett


/--
[exists_hyperbolic_pair_of_isotropic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/CorBilinearHermitianForms.lean)
-/
@[path]
private lemma main
  [Field k]
  [Invertible (2 : k)]
  [AddCommGroup V]
  [Module k V]
  {B : LinearMap.BilinForm k V}
  {v : V}
-- given
  (hBnd : B.Nondegenerate)
  (hBsymm : B.IsSymm)
  (hv : v ≠ 0)
  (hiso : B v v = 0) :
-- imply
  ∃ w : V, B v w = 1 ∧ B w w = 0 ∧ B w v = 1 := by
-- proof
  have ⟨y, hy⟩ : ∃ y, B v y ≠ 0 := by
    by_contra hall; push Not at hall; exact hv (hBnd.1 v hall)
  set y' := (B v y)⁻¹ • y
  have hvy' : B v y' = 1 := by
    simp only [y', map_smul, smul_eq_mul]; exact inv_mul_cancel₀ hy
  have hy'v : B y' v = 1 := by rw [hBsymm.eq y' v]; exact hvy'
  set c := ⅟(2 : k) * B y' y'
  set w := y' - c • v
  have hvw : B v w = 1 := by
    show B v (y' - c • v) = 1
    simp only [map_sub, map_smul, smul_eq_mul, hvy', hiso, mul_zero, sub_zero]
  have hwv : B w v = 1 := by rw [hBsymm.eq]; exact hvw
  have hww : B w w = 0 := by
    show B (y' - c • v) (y' - c • v) = 0
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
      hiso, hy'v, hvy', mul_one, mul_zero, sub_zero, c]
    have : ⅟(2 : k) * B y' y' + ⅟(2 : k) * B y' y' = B y' y' := by
      rw [← add_mul, ← two_mul, mul_invOf_self, one_mul]
    linear_combination -this
  exact ⟨w, hvw, hww, hwv⟩



/--
[restrict_orthogonal_nondegenerate](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/CorBilinearHermitianForms.lean)
-/
private lemma restrict_orthogonal_nondegenerate
  [Field k]
  [Invertible (2 : k)]
  [AddCommGroup V]
  [Module k V]
  [FiniteDimensional k V]
  {B : LinearMap.BilinForm k V}
  {P : Submodule k V}
-- given
  (hBnd : B.Nondegenerate)
  (hBrefl : B.IsRefl)
  (hP : (B.restrict P).Nondegenerate) :
-- imply
  (B.restrict (B.orthogonal P)).Nondegenerate := by
-- proof
  rw [LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal hBrefl]
  rw [LinearMap.BilinForm.orthogonal_orthogonal hBnd hBrefl P]
  exact (B.isCompl_orthogonal_of_restrict_nondegenerate hBrefl hP).symm



/--
[restrict_isSymm'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/CorBilinearHermitianForms.lean)
-/
private lemma restrict_isSymm'
  [Field k]
  [Invertible (2 : k)]
  [AddCommGroup V]
  [Module k V]
  {B : LinearMap.BilinForm k V}
  {W : Submodule k V}
-- given
  (hBsymm : B.IsSymm) :
-- imply
  (B.restrict W).IsSymm := by
-- proof
  constructor; intro ⟨x, _⟩ ⟨y, _⟩
  simp only [LinearMap.BilinForm.restrict_apply]; exact hBsymm.eq x y



/--
[restrict_bot_nondegenerate'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/CorBilinearHermitianForms.lean)
-/
private lemma restrict_bot_nondegenerate'
  [Field k]
  [Invertible (2 : k)]
  [AddCommGroup V]
  [Module k V]
  {B : LinearMap.BilinForm k V} :
-- imply
  (B.restrict (⊥ : Submodule k V)).Nondegenerate := by
-- proof
  constructor <;> intro ⟨m, hm⟩ _ <;>
    simp only [Submodule.mem_bot] at hm <;> exact Subtype.ext hm



/--
[orthogonal_bot'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/CorBilinearHermitianForms.lean)
-/
private lemma orthogonal_bot'
  [Field k]
  [Invertible (2 : k)]
  [AddCommGroup V]
  [Module k V]
  {B : LinearMap.BilinForm k V} :
-- imply
  B.orthogonal ⊥ = ⊤ := by
-- proof
  ext x; simp



/--
[restrict_top_anisotropic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/CorBilinearHermitianForms.lean)
-/
private lemma restrict_top_anisotropic
  [Field k]
  [Invertible (2 : k)]
  [AddCommGroup V]
  [Module k V]
  {B : LinearMap.BilinForm k V}
-- given
  (hB : BilinForm.IsAnisotropicOn B ⊤) :
-- imply
  BilinForm.IsAnisotropicOn (B.restrict (⊤ : Submodule k V)) ⊤ := by
-- proof
  intro ⟨x, _⟩ _ hx
  simp only [LinearMap.BilinForm.restrict_apply] at hx
  exact Subtype.ext (hB x (Submodule.mem_top) hx)



/--
[orthogonal_sup_map_eq'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/CorBilinearHermitianForms.lean)
-/
private lemma orthogonal_sup_map_eq'
  [Field k]
  [Invertible (2 : k)]
  [AddCommGroup V]
  [Module k V]
  {B : LinearMap.BilinForm k V}
  {P Pperp : Submodule k V}
  {H' : Submodule k ↥Pperp}
-- given
  (hPperp : Pperp = B.orthogonal P) :
-- imply
  B.orthogonal (P ⊔ H'.map Pperp.subtype) = ((B.restrict Pperp).orthogonal H').map Pperp.subtype := by
-- proof
  ext x; constructor
  · intro hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at hx
    have hxP : x ∈ Pperp := by
      rw [hPperp, LinearMap.BilinForm.mem_orthogonal_iff]
      intro p hp; exact hx p (Submodule.mem_sup_left hp)
    exact Submodule.mem_map.mpr ⟨⟨x, hxP⟩, by
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro ⟨h', _⟩ hh'H
      exact hx h' (Submodule.mem_sup_right (Submodule.mem_map_of_mem hh'H)), rfl⟩
  · intro hx
    obtain ⟨⟨x', hx'P⟩, hx'H, rfl⟩ := Submodule.mem_map.mp hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hy
    show B (p + q) x' = 0
    rw [map_add, LinearMap.add_apply,
      show B p x' = 0 from by rw [hPperp] at hx'P; exact hx'P p hp,
      show B q x' = 0 from by
        obtain ⟨q', hq'H, rfl⟩ := Submodule.mem_map.mp hq
        exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hx'H) q' hq'H,
      add_zero]



/--
[isCompl_lift_submodule'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/CorBilinearHermitianForms.lean)
-/
private lemma isCompl_lift_submodule'
  [Field k]
  [Invertible (2 : k)]
  [AddCommGroup V]
  [Module k V]
  {P Pperp : Submodule k V}
  {H' A' : Submodule k ↥Pperp}
-- given
  (hCompl : IsCompl P Pperp)
  (hHA : IsCompl H' A') :
-- imply
  IsCompl (P ⊔ H'.map Pperp.subtype) (A'.map Pperp.subtype) := by
-- proof
  constructor
  · rw [disjoint_iff]; ext x
    simp only [Submodule.mem_inf, Submodule.mem_bot]; constructor
    · intro ⟨hx_sup, hx_A⟩
      have hxPperp : x ∈ Pperp := by
        obtain ⟨a, _, rfl⟩ := Submodule.mem_map.mp hx_A; exact a.2
      obtain ⟨p, hp, h', hh', rfl⟩ := Submodule.mem_sup.mp hx_sup
      have hh'Pperp : h' ∈ Pperp := by
        obtain ⟨h'', _, rfl⟩ := Submodule.mem_map.mp hh'; exact h''.2
      have hp0 : p = 0 := by
        have hpPperp : p ∈ Pperp := by
          have hsub : p = (p + h') - h' := by abel
          rw [hsub]; exact Pperp.sub_mem hxPperp hh'Pperp
        have : p ∈ P ⊓ Pperp := Submodule.mem_inf.mpr ⟨hp, hpPperp⟩
        rwa [hCompl.inf_eq_bot, Submodule.mem_bot] at this
      rw [hp0, zero_add]; rw [hp0, zero_add] at hx_A
      obtain ⟨h'', hh''H, rfl⟩ := Submodule.mem_map.mp hh'
      obtain ⟨a', ha'A, ha'eq⟩ := Submodule.mem_map.mp hx_A
      have : h'' ∈ H' ⊓ A' := Submodule.mem_inf.mpr ⟨hh''H,
        (Subtype.val_injective ha'eq.symm : h'' = a') ▸ ha'A⟩
      rw [hHA.inf_eq_bot, Submodule.mem_bot] at this; simp [this]
    · intro h; simp [h]
  · rw [codisjoint_iff, sup_assoc,
    show H'.map Pperp.subtype ⊔ A'.map Pperp.subtype = Pperp from by
      rw [← Submodule.map_sup, hHA.sup_eq_top]
      simp [Submodule.map_top, Submodule.range_subtype]]
    exact hCompl.sup_eq_top



/--
[isAnisotropic_restrict_map](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/CorBilinearHermitianForms.lean)
-/
private lemma isAnisotropic_restrict_map
  [Field k]
  [Invertible (2 : k)]
  [AddCommGroup V]
  [Module k V]
  {B : LinearMap.BilinForm k V}
  {W : Submodule k V}
  {A : Submodule k ↥W}
-- given
  (hA : BilinForm.IsAnisotropicOn ((B.restrict W).restrict A) ⊤) :
-- imply
  BilinForm.IsAnisotropicOn (B.restrict (A.map W.subtype)) ⊤ := by
-- proof
  intro ⟨x, hx⟩ _ hBx
  obtain ⟨⟨a, haW⟩, haA, rfl⟩ := Submodule.mem_map.mp hx
  have h := hA ⟨⟨a, haW⟩, haA⟩ Submodule.mem_top hBx
  simp only [Subtype.ext_iff] at h; exact Subtype.ext h



/--
[garrett_7_2_corollary](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/CorBilinearHermitianForms.lean)
-/
private lemma garrett_7_2_corollary
  [Field k]
  [Invertible (2 : k)]
  [AddCommGroup V]
  [Module k V]
  [FiniteDimensional k V]
  {B : LinearMap.BilinForm k V}
-- given
  (hBnd : B.Nondegenerate)
  (hBsymm : B.IsSymm) :
-- imply
  ∃ (H : Submodule k V), BilinForm.IsHyperbolicSubspace' B H ∧ (B.restrict H).Nondegenerate ∧ BilinForm.IsAnisotropicOn B (B.orthogonal H) := by
-- proof
  induction hn : Module.finrank k V using Nat.strongRecOn generalizing V with
  | _ n ih =>
  by_cases hAniso : ∀ x : V, B x x = 0 → x = 0
  · refine ⟨⊥, ?_, restrict_bot_nondegenerate' B, ?_⟩
    · exact ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0,
      fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
      fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
      by simp [Set.range_eq_empty]⟩
    · rw [orthogonal_bot']
      intro x _ hBxx; exact hAniso x hBxx
  · push Not at hAniso
    obtain ⟨v, hiso, hv⟩ := hAniso
    obtain ⟨w, hvw, hww, hwv⟩ := exists_hyperbolic_pair_of_isotropic B hBnd hBsymm v hv hiso
    set P := Submodule.span k {v, w} with hP_def
    have hPnd : (B.restrict P).Nondegenerate := by
      rw [LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal hBsymm.isRefl]
      rw [LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint hBsymm.isRefl]
      rw [disjoint_iff]
      ext x; constructor
      · intro hx
        obtain ⟨hxP, hxPerp⟩ := Submodule.mem_inf.mp hx
        have hxv : B x v = 0 := by
          have hv_mem : v ∈ P := Submodule.subset_span (Set.mem_insert v {w})
          exact hBsymm.eq v x ▸ hxPerp v hv_mem
        have hxw : B x w = 0 := by
          have hw_mem : w ∈ P := Submodule.subset_span (Set.mem_insert_iff.mpr (Or.inr rfl))
          exact hBsymm.eq w x ▸ hxPerp w hw_mem
        rw [Submodule.mem_span_insert] at hxP
        obtain ⟨a, z, hz, hxeq⟩ := hxP
        rw [Submodule.mem_span_singleton] at hz; obtain ⟨b, rfl⟩ := hz
        rw [show x = a • v + b • w from hxeq] at hxv hxw
        simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
          at hxv hxw
        rw [hiso, hwv, mul_zero, zero_add, mul_one] at hxv
        rw [hvw, hww, mul_one, mul_zero, add_zero] at hxw
        rw [hxeq, hxv, hxw, zero_smul, zero_smul, add_zero]
        exact Submodule.zero_mem _
      · intro hx; rw [(Submodule.mem_bot k).mp hx]; exact Submodule.zero_mem _
    have hCompl : IsCompl P (B.orthogonal P) :=
      B.isCompl_orthogonal_of_restrict_nondegenerate hBsymm.isRefl hPnd
    have hPerpNd : (B.restrict (B.orthogonal P)).Nondegenerate :=
      restrict_orthogonal_nondegenerate B hBnd hBsymm.isRefl P hPnd
    have hPerpRank : Module.finrank k ↥(B.orthogonal P) < n := by
      rw [← hn]; apply Submodule.finrank_lt; intro h
      rw [h] at hCompl; have := hCompl.inf_eq_bot; simp only [inf_top_eq] at this
      have hv_mem : v ∈ P := Submodule.subset_span (Set.mem_insert v {w})
      rw [this] at hv_mem; exact hv ((Submodule.mem_bot k).mp hv_mem)
    set Pperp := B.orthogonal P
    have hPerpSymm := restrict_isSymm' B hBsymm Pperp
    obtain ⟨H', hH'hyp, hH'nd, hH'aniso⟩ :=
      ih _ hPerpRank (B.restrict Pperp) hPerpNd hPerpSymm rfl
    set H'V := H'.map Pperp.subtype
    set H := P ⊔ H'V
    set A' := (B.restrict Pperp).orthogonal H'
    have hOrthH : B.orthogonal H = A'.map Pperp.subtype :=
      orthogonal_sup_map_eq' B P Pperp rfl H'
    have hHA : IsCompl H' A' :=
      (B.restrict Pperp).isCompl_orthogonal_of_restrict_nondegenerate
        (restrict_isSymm' B hBsymm Pperp).isRefl hH'nd
    have hHCompl : IsCompl H (B.orthogonal H) := by
      rw [hOrthH]; exact isCompl_lift_submodule' P Pperp hCompl H' A' hHA
    have hHhyp : BilinForm.IsHyperbolicSubspace' B H := by
      obtain ⟨m, vs', ws', hvs'H, hws'H, hvs'iso, hws'iso, hvw'pair,
        hvv'orth, hww'orth, hvw'orth, hH'span⟩ := hH'hyp
      let vs0 : Fin m → V := fun i => (vs' i : V)
      let ws0 : Fin m → V := fun i => (ws' i : V)
      refine ⟨m + 1, Fin.cons v vs0, Fin.cons w ws0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i; refine Fin.cases ?_ (fun j => ?_) i
        · exact Submodule.mem_sup_left (Submodule.subset_span (Set.mem_insert v {w}))
        · exact Submodule.mem_sup_right (Submodule.mem_map_of_mem (hvs'H j))
      · intro i; refine Fin.cases ?_ (fun j => ?_) i
        · exact Submodule.mem_sup_left (Submodule.subset_span (Set.mem_insert_iff.mpr (Or.inr rfl)))
        · exact Submodule.mem_sup_right (Submodule.mem_map_of_mem (hws'H j))
      · intro i; refine Fin.cases ?_ (fun j => ?_) i; exact hiso; exact hvs'iso j
      · intro i; refine Fin.cases ?_ (fun j => ?_) i; exact hww; exact hws'iso j
      · intro i; refine Fin.cases ?_ (fun j => ?_) i; exact hvw; exact hvw'pair j
      · intro i j hij; revert hij
        refine Fin.cases ?_ (fun a => ?_) i <;> refine Fin.cases ?_ (fun b => ?_) j <;> intro hij
        · exact absurd rfl hij
        · exact (vs' b).2 v (Submodule.subset_span (Set.mem_insert v {w}))
        · rw [hBsymm.eq]; exact (vs' a).2 v (Submodule.subset_span (Set.mem_insert v {w}))
        · exact hvv'orth a b (fun h => hij (congrArg Fin.succ h))
      · intro i j hij; revert hij
        refine Fin.cases ?_ (fun a => ?_) i <;> refine Fin.cases ?_ (fun b => ?_) j <;> intro hij
        · exact absurd rfl hij
        · exact (ws' b).2 w (Submodule.subset_span (Set.mem_insert_iff.mpr (Or.inr rfl)))
        · rw [hBsymm.eq]; exact (ws' a).2 w (Submodule.subset_span (Set.mem_insert_iff.mpr (Or.inr rfl)))
        · exact hww'orth a b (fun h => hij (congrArg Fin.succ h))
      · intro i j hij; revert hij
        refine Fin.cases ?_ (fun a => ?_) i <;> refine Fin.cases ?_ (fun b => ?_) j <;> intro hij
        · exact absurd rfl hij
        · exact (ws' b).2 v (Submodule.subset_span (Set.mem_insert v {w}))
        · rw [hBsymm.eq]; exact (vs' a).2 w (Submodule.subset_span (Set.mem_insert_iff.mpr (Or.inr rfl)))
        · exact hvw'orth a b (fun h => hij (congrArg Fin.succ h))
      · have hvs0_range : Set.range vs0 = Pperp.subtype '' Set.range vs' := by
        ext x; simp [vs0, Set.mem_range, Set.mem_image]
        have hws0_range : Set.range ws0 = Pperp.subtype '' Set.range ws' := by
          ext x; simp [ws0, Set.mem_range, Set.mem_image]
        rw [show H = P ⊔ H'V from rfl, show H'V = H'.map Pperp.subtype from rfl]
        rw [hH'span, Submodule.map_span]
        simp only [Fin.range_cons, Set.image_union]
        rw [← hvs0_range, ← hws0_range, show P = Submodule.span k {v, w} from rfl,
          ← Submodule.span_union]
        congr 1; ext x
        simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range]
        tauto
    have hAniso' : BilinForm.IsAnisotropicOn B (B.orthogonal H) := by
      rw [hOrthH]
      intro x hx hBxx
      obtain ⟨⟨a, haW⟩, haA, rfl⟩ := Submodule.mem_map.mp hx
      exact Subtype.ext_iff.mp (hH'aniso ⟨a, haW⟩ (by
        rw [LinearMap.BilinForm.mem_orthogonal_iff]
        intro ⟨h', hh'W⟩ hh'H'
        have : (⟨a, haW⟩ : Pperp) ∈ (B.restrict Pperp).orthogonal H' := by
          rw [← hOrthH] at hx
          rw [LinearMap.BilinForm.mem_orthogonal_iff]
          intro y hy
          have hyH : (y : V) ∈ H := Submodule.mem_sup_right (Submodule.mem_map_of_mem hy)
          exact LinearMap.BilinForm.mem_orthogonal_iff.mp hx (y : V) hyH
        exact LinearMap.BilinForm.mem_orthogonal_iff.mp this ⟨h', hh'W⟩ hh'H') hBxx)
    exact ⟨H, hHhyp,
      (LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal hBsymm.isRefl).mpr hHCompl,
      hAniso'⟩



-- created on 2026-10-23
-- updated on 2026-10-26
