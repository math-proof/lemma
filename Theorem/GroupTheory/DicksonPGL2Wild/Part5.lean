/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/DicksonPGL2Wild.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import Theorem.GroupTheory.DicksonPGL2Tame.Part4
import Lemma.Nat.Card_Stabilizer
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.Algebra.Group.IsCommutative
import Mathlib.Algebra.Module.ZMod
import Mathlib.FieldTheory.Separable
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.SchurZassenhaus
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import Def.GroupTheory.DicksonPGL2Wild.Part7
/-!
# Dickson's classification in the wild case

This file classifies finite subgroups of `PGL₂` over an algebraic closure of an odd finite
field when the characteristic divides the group order. It also supplies the projective linear
group order formulas and characteristic-order element facts used by the classification.
-/


namespace MetaMathlibExt

namespace Dickson

open scoped BigOperators Pointwise Polynomial

namespace DicksonWildAffine

lemma rightRestrict_range_card_add_one_le_multiplierSubfield
    {F : Type*} [Field F] (H : Subgroup (Aff F)) [Finite H]
    (hΓ : translationAddSubgroup H ≠ ⊥) :
    Nat.card (rightRestrict H).range + 1 ≤
      Nat.card (multiplierSubfield (translationAddSubgroup H)) := by
  let _ : Finite (rightRestrict H).range := Finite.of_surjective
    (rightRestrict H).rangeRestrict (rightRestrict H).rangeRestrict_surjective
  let _ : Finite (multiplierSubfield (translationAddSubgroup H)) :=
    multiplierSubfield_finite (translationAddSubgroup H) hΓ
  let toM : Option (rightRestrict H).range →
      multiplierSubfield (translationAddSubgroup H)
    | none => 0
    | some u => ⟨u.1, rightRestrict_range_mem_multiplierSubfield H u⟩
  have htoM : Function.Injective toM := by
    intro a b hab
    cases a with
    | none =>
        cases b with
        | none => rfl
        | some b =>
            exfalso
            have h := congrArg Subtype.val hab
            exact b.1.ne_zero (by simpa [toM] using h.symm)
    | some a =>
        cases b with
        | none =>
            exfalso
            have h := congrArg Subtype.val hab
            simp [toM] at h
        | some b =>
            congr 1
            apply Subtype.ext
            apply Units.ext
            exact congrArg Subtype.val hab
  let _ : Fintype (rightRestrict H).range := Fintype.ofFinite _
  let _ : Fintype (multiplierSubfield (translationAddSubgroup H)) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    ← Fintype.card_option]
  exact Fintype.card_le_of_injective toM htoM

lemma multiplierSubfield_card_eq_pow
    {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
    {F : Type*} [Field F] [CharP F p]
    (H : Subgroup (Aff F)) [Finite H] (m t : ℕ) (hm : 1 ≤ m)
    (hHcard : Nat.card H = p ^ m * t)
    (hrange : Nat.card (rightRestrict H).range = t)
    (hsandwich : p ^ m - 1 ≤ 2 * t) :
    Nat.card (multiplierSubfield (translationAddSubgroup H)) = p ^ m := by
  let Γ := translationAddSubgroup H
  have hΓcard : Nat.card Γ = p ^ m :=
    translationAddSubgroup_card_eq H (p ^ m) t hHcard hrange
  have hqone : 1 < p ^ m :=
    one_lt_pow₀ (Fact.out : p.Prime).one_lt (by omega)
  have hΓ : Γ ≠ ⊥ := by
    intro h
    rw [h] at hΓcard
    simp at hΓcard
    omega
  let M := multiplierSubfield Γ
  let _ : Finite M := multiplierSubfield_finite Γ hΓ
  let _ : Fintype M := Fintype.ofFinite M
  obtain ⟨ell, -, hMpow⟩ := FiniteField.card M p
  have hMpow' : Nat.card M = p ^ (ell : ℕ) := by
    rw [Nat.card_eq_fintype_card]
    exact hMpow
  have hMle : Nat.card M ≤ p ^ m := by
    rw [← hΓcard]
    exact multiplierSubfield_card_le Γ hΓ
  have hellm : (ell : ℕ) ≤ m := by
    apply (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp
    rwa [← hMpow']
  have htM : t + 1 ≤ Nat.card M := by
    have := rightRestrict_range_card_add_one_le_multiplierSubfield H hΓ
    rwa [hrange] at this
  have hell : (ell : ℕ) = m := by
    by_contra hne
    have hellsucc : (ell : ℕ) + 1 ≤ m := by omega
    have hpstep : p ^ ((ell : ℕ) + 1) ≤ p ^ m :=
      Nat.pow_le_pow_right (Fact.out : p.Prime).pos hellsucc
    have hp3 : 3 ≤ p := by
      have hpgt : 2 < p := Fact.out
      exact hpgt
    have hthree : 3 * Nat.card M ≤ p ^ m := by
      calc
        3 * Nat.card M = p ^ (ell : ℕ) * 3 := by rw [hMpow']; omega
        _ ≤ p ^ (ell : ℕ) * p := Nat.mul_le_mul_left _ hp3
        _ = p ^ ((ell : ℕ) + 1) := (pow_succ _ _).symm
        _ ≤ p ^ m := hpstep
    have hMpos : 0 < Nat.card M := Nat.card_pos
    omega
  rw [hMpow', hell]

lemma exists_affine_normal_form
    {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
    {F : Type*} [Field F] [CharP F p]
    (H : Subgroup (Aff F)) [Finite H] (m t : ℕ) (hm : 1 ≤ m)
    (hHcard : Nat.card H = p ^ m * t)
    (hrange : Nat.card (rightRestrict H).range = t)
    (hsandwich : p ^ m - 1 ≤ 2 * t) :
    ∃ (s : F) (γ : translationAddSubgroup H)
      (coord : H → multiplierSubfield (translationAddSubgroup H) × multiplierRange H),
      (γ : F) ≠ 0 ∧ Function.Bijective coord ∧
      ∀ h : H,
        (((coord h).1 : multiplierSubfield (translationAddSubgroup H)) : F) * γ.1 =
          ((SemidirectProduct.inl (Multiplicative.ofAdd s) * h.1 *
            (SemidirectProduct.inl (Multiplicative.ofAdd s) : Aff F)⁻¹).left).toAdd ∧
        (((((coord h).2.1 :
          (multiplierSubfield (translationAddSubgroup H))ˣ) :
            multiplierSubfield (translationAddSubgroup H)) : F)) =
          ((h.1 : Aff F).right : F) := by
  classical
  let Γ := translationAddSubgroup H
  let M := multiplierSubfield Γ
  let L := multiplierRange H
  have hΓcard : Nat.card Γ = p ^ m :=
    translationAddSubgroup_card_eq H (p ^ m) t hHcard hrange
  have hΓ : Γ ≠ ⊥ := by
    intro h
    rw [h] at hΓcard
    simp at hΓcard
    have hqone : 1 < p ^ m :=
      one_lt_pow₀ (Fact.out : p.Prime).one_lt (by omega)
    omega
  let _ : Finite M := multiplierSubfield_finite Γ hΓ
  let _ : Finite (rightRestrict H).range := Finite.of_surjective
    (rightRestrict H).rangeRestrict (rightRestrict H).rangeRestrict_surjective
  let _ : Finite L := Finite.of_surjective (multiplierRangeHom H).rangeRestrict
    (multiplierRangeHom H).rangeRestrict_surjective
  have hMcard : Nat.card M = p ^ m :=
    multiplierSubfield_card_eq_pow H m t hm hHcard hrange hsandwich
  have hLcard : Nat.card L = t := (multiplierRange_card H).trans hrange
  obtain ⟨γ, hγ⟩ := AddSubgroup.ne_bot_iff_exists_ne_zero.mp hΓ
  have hγval : (γ : F) ≠ 0 := by
    intro h
    exact hγ (Subtype.ext h)
  let toΓ : M → Γ := fun a ↦ ⟨a.1 * γ.1, a.2 γ.1 γ.2⟩
  have htoΓ : Function.Bijective toΓ :=
    multiplier_mul_bijective Γ hΓ γ hγval (hMcard.trans hΓcard.symm)
  let eΓ : M ≃ Γ := Equiv.ofBijective toΓ htoΓ
  obtain ⟨s, hs⟩ := exists_translation_conj_left_mem H
  let normLeft (h : H) : Γ := ⟨
    ((SemidirectProduct.inl (Multiplicative.ofAdd s) * h.1 *
      (SemidirectProduct.inl (Multiplicative.ofAdd s) : Aff F)⁻¹).left).toAdd,
    hs h⟩
  let rangeCoord (h : H) : (rightRestrict H).range :=
    ⟨rightRestrict H h, ⟨h, rfl⟩⟩
  let coord : H → M × L := fun h ↦
    (eΓ.symm (normLeft h),
      ⟨multiplierRangeHom H (rangeCoord h), ⟨rangeCoord h, rfl⟩⟩)
  have hcoordInj : Function.Injective coord := by
    intro h k hhk
    have hleftCoord := congrArg Prod.fst hhk
    have hrightCoord := congrArg Prod.snd hhk
    have hnorm : normLeft h = normLeft k := eΓ.symm.injective hleftCoord
    have hrangeCoord : rangeCoord h = rangeCoord k := by
      apply multiplierRangeHom_injective H
      exact congrArg Subtype.val hrightCoord
    have hright : (h.1 : Aff F).right = (k.1 : Aff F).right :=
      congrArg (fun u : (rightRestrict H).range ↦ u.1) hrangeCoord
    let T : Aff F := SemidirectProduct.inl (Multiplicative.ofAdd s)
    have hconj : T * h.1 * T⁻¹ = T * k.1 * T⁻¹ := by
      apply SemidirectProduct.ext
      · exact Multiplicative.ext (congrArg Subtype.val hnorm)
      · simp [T, SemidirectProduct.mul_right, SemidirectProduct.inv_right, hright]
    apply Subtype.ext
    exact (MulAut.conj T).injective hconj
  have hcoord : Function.Bijective coord := by
    let _ : Fintype H := Fintype.ofFinite H
    let _ : Fintype M := Fintype.ofFinite M
    let _ : Fintype L := Fintype.ofFinite L
    apply (Fintype.bijective_iff_injective_and_card coord).2
    refine ⟨hcoordInj, ?_⟩
    simp only [← Nat.card_eq_fintype_card, Nat.card_prod, hHcard, hMcard,
      hLcard]
  refine ⟨s, γ, coord, hγval, hcoord, ?_⟩
  intro h
  constructor
  · have he := eΓ.apply_symm_apply (normLeft h)
    exact congrArg Subtype.val he
  · rfl

lemma exists_affine_matrix_normal_form
    {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
    {F : Type*} [Field F] [CharP F p]
    (H : Subgroup (Aff F)) [Finite H] (m t : ℕ) (hm : 1 ≤ m)
    (hHcard : Nat.card H = p ^ m * t)
    (hrange : Nat.card (rightRestrict H).range = t)
    (hsandwich : p ^ m - 1 ≤ 2 * t) :
    ∃ (M : Subfield F) (c : GL (Fin 2) F) (L : Subgroup Mˣ)
      (coord : H → M × L),
      Finite M ∧ Nat.card M = p ^ m ∧ Nat.card L = t ∧
      Function.Bijective coord ∧
      (∀ A : GL (Fin 2) F, A 1 0 ≠ 0 →
        ((c * A * c⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0) ∧
      ∀ h : H,
        c * affineGL h.1.left.toAdd h.1.right * c⁻¹ =
          Matrix.GeneralLinearGroup.map M.subtype
            (affineGL (coord h).1 (coord h).2.1) := by
  classical
  let Γ := translationAddSubgroup H
  let M := multiplierSubfield Γ
  let L := multiplierRange H
  obtain ⟨s, γ, coord, hγ, hcoord, hform⟩ :=
    exists_affine_normal_form H m t hm hHcard hrange hsandwich
  let r : Fˣ := Units.mk0 (γ.1)⁻¹ (inv_ne_zero hγ)
  let T : GL (Fin 2) F := affineGL s 1
  let D : GL (Fin 2) F := affineGL 0 r
  let c : GL (Fin 2) F := D * T
  have hMfinite : Finite M := by
    apply multiplierSubfield_finite Γ
    intro hbot
    apply hγ
    have hmem : (γ : F) ∈ Γ := γ.2
    rw [hbot] at hmem
    exact hmem
  let _ : Finite M := hMfinite
  have hMcard : Nat.card M = p ^ m :=
    multiplierSubfield_card_eq_pow H m t hm hHcard hrange hsandwich
  have hLcard : Nat.card L = t := (multiplierRange_card H).trans hrange
  refine ⟨M, c, L, coord, hMfinite, hMcard, hLcard, hcoord, ?_, ?_⟩
  · intro A hA
    have hcshape : c = affineGL ((r : F) * s) r := by
      dsimp [c, D, T]
      rw [affineGL_mul]
      simp
    rw [hcshape, affineGL_conj_lowerLeft]
    exact mul_ne_zero hA (inv_ne_zero r.ne_zero)
  intro h
  have hformh := hform h
  rw [translation_conj_left] at hformh
  have hconj : c * affineGL h.1.left.toAdd h.1.right * c⁻¹ =
      D * (T * affineGL h.1.left.toAdd h.1.right * T⁻¹) * D⁻¹ := by
    dsimp [c]
    group
  rw [hconj]
  change D * (affineGL s 1 * affineGL h.1.left.toAdd h.1.right *
    (affineGL s 1)⁻¹) * D⁻¹ = _
  rw [affineGL_translation_conj]
  change affineGL 0 r *
      affineGL (h.1.left.toAdd + (1 - (h.1.right : F)) * s) h.1.right *
      (affineGL 0 r)⁻¹ = _
  rw [affineGL_conj, affineGL_map_subfield]
  congr 2
  · change (γ.1)⁻¹ *
        (h.1.left.toAdd + (1 - (h.1.right : F)) * s) = ((coord h).1 : F)
    rw [← hformh.1]
    field_simp
  · apply Units.ext
    exact hformh.2.symm

lemma card_parabolic_borel_fiber_le_two {F : Type*} [Field F]
    (S : GL (Fin 2) F)
    (hS10 : (S : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0)
    (H : Subgroup (borel F)) [Finite H] (u : Fˣ) :
    Nat.card {h : H // lambda h.1 = u ∧
      (((S * affineGL (gamma h.1) (lambda h.1) : GL (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F)).IsParabolic} ≤ 2 := by
  classical
  let c : F := 4 * Matrix.det (S : Matrix (Fin 2) (Fin 2) F) * (u : F)
  let toRoot : {h : H // lambda h.1 = u ∧
      (((S * affineGL (gamma h.1) (lambda h.1) : GL (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F)).IsParabolic} →
      {x : F // x ^ 2 = c} := fun h ↦ ⟨
    Matrix.trace (((S * affineGL (gamma h.1.1) (lambda h.1.1) : GL (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F)), by
      rw [h.2.1]
      have hdisc := h.2.2.2
      rw [Matrix.discr_fin_two, h.2.1] at hdisc
      have heq := sub_eq_zero.mp hdisc
      rw [det_mul_affineGL] at heq
      simpa [c, mul_assoc] using heq⟩
  have hinj : Function.Injective toRoot := by
    intro x y hxy
    have htrace := congrArg (fun z : {w : F // w ^ 2 = c} ↦ z.1) hxy
    change Matrix.trace (((S * affineGL (gamma x.1.1) (lambda x.1.1) :
        GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) =
      Matrix.trace (((S * affineGL (gamma y.1.1) (lambda y.1.1) :
        GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) at htrace
    rw [trace_mul_affineGL, trace_mul_affineGL, x.2.1, y.2.1] at htrace
    have hgamma : gamma x.1.1 = gamma y.1.1 := by
      apply mul_left_cancel₀ hS10
      linear_combination htrace
    apply Subtype.ext
    apply Subtype.ext
    apply toAff_injective
    apply SemidirectProduct.ext
    · exact hgamma
    · exact x.2.1.trans y.2.1.symm
  let q : F[X] := Polynomial.X ^ 2 - Polynomial.C c
  have hq0 : q ≠ 0 := Polynomial.X_pow_sub_C_ne_zero (by decide) c
  have hfinite : Set.Finite {x : F | x ^ 2 = c} := by
    apply (Finset.finite_toSet (q.map (algebraMap F F)).roots.toFinset).subset
    intro x hx
    rw [show (q.map (algebraMap F F)).roots.toFinset = q.rootSet F by rfl,
      Polynomial.mem_rootSet_of_ne hq0]
    change x ^ 2 = c at hx
    simpa [q] using sub_eq_zero.mpr hx
  let _ : Fintype {x : F // x ^ 2 = c} := hfinite.fintype
  exact (Nat.card_le_card_of_injective toRoot hinj).trans
    (card_quadraticFiber_le_two c)

lemma card_parabolic_borel_le_twice_range {F : Type*} [Field F]
    (S : GL (Fin 2) F)
    (hS10 : (S : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0)
    (H : Subgroup (borel F)) [Finite H] :
    Nat.card {h : H //
      (((S * affineGL (gamma h.1) (lambda h.1) : GL (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F)).IsParabolic} ≤
      2 * Nat.card (SemidirectProduct.rightHom.comp
        (toAff.comp H.subtype)).range := by
  classical
  let rhoH : H →* Fˣ := SemidirectProduct.rightHom.comp (toAff.comp H.subtype)
  let E := {h : H //
    (((S * affineGL (gamma h.1) (lambda h.1) : GL (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F)).IsParabolic}
  let toRange : E → rhoH.range := fun h ↦ ⟨rhoH h.1, ⟨h.1, rfl⟩⟩
  let _ : Finite rhoH.range := Finite.of_surjective rhoH.rangeRestrict
    rhoH.rangeRestrict_surjective
  have hfiber (u : rhoH.range) : Nat.card {h : E // toRange h = u} ≤ 2 := by
    let toFixed : {h : E // toRange h = u} →
        {h : H // lambda h.1 = u.1 ∧
          (((S * affineGL (gamma h.1) (lambda h.1) : GL (Fin 2) F) :
            Matrix (Fin 2) (Fin 2) F)).IsParabolic} := fun h ↦
      ⟨h.1.1, congrArg (fun z : rhoH.range ↦ z.1) h.2, h.1.2⟩
    have hinj : Function.Injective toFixed := by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z ↦ z.1) hxy
    exact (Nat.card_le_card_of_injective toFixed hinj).trans
      (card_parabolic_borel_fiber_le_two S hS10 H u.1)
  simpa [E, rhoH] using card_le_mul_card_of_fiber_le toRange 2 hfiber

end DicksonWildAffine

lemma dicksonWild_normalizer_borel_coordinates
    {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
    (G : Subgroup (PGL p)) [Finite G] (hpG : p ∣ Nat.card G) (P : Sylow p G) :
    ∃ (a : MulAut (PGL p))
      (B : Subgroup (DicksonWildAffine.borel (K p)))
      (e : Subgroup.normalizer (P : Set G) ≃* B),
      (∀ n, ((e n).1 : PGL p) = a (n.1 : PGL p)) ∧
      ∀ g : G, g ∉ Subgroup.normalizer (P : Set G) →
        (DicksonWildAffine.lift (a (g : PGL p)) :
          Matrix (Fin 2) (Fin 2) (K p)) 1 0 ≠ 0 := by
  classical
  let N := Subgroup.normalizer (P : Set G)
  let Pbar : Subgroup (PGL p) := Subgroup.map G.subtype (P : Subgroup G)
  let eP : (P : Subgroup G) ≃* Pbar :=
    Subgroup.equivMapOfInjective (P : Subgroup G) G.subtype G.subtype_injective
  let _ : Finite Pbar := Finite.of_surjective eP eP.surjective
  have hPbar : IsPGroup p Pbar := P.isPGroup'.map G.subtype
  have hPbarNe : Pbar ≠ ⊥ := by
    change Subgroup.map G.subtype (P : Subgroup G) ≠ ⊥
    intro h
    apply dicksonWild_sylow_ne_bot_of_dvd_card P hpG
    exact (Subgroup.map_eq_bot_iff_of_injective (P : Subgroup G)
      G.subtype_injective).mp h
  obtain ⟨x, hx, hunique⟩ :=
    dicksonWild_existsUnique_fixedPoint_of_isPGroup Pbar hPbar hPbarNe
  have hPfix (z : P) : (z.1 : PGL p) • x = x := by
    change (eP z : PGL p) • x = x
    exact hx (eP z)
  have hPunique (y : Projectivization (K p) (Fin 2 → K p))
      (hy : ∀ z : P, (z.1 : PGL p) • y = y) : y = x := by
    apply hunique
    intro z
    obtain ⟨w, rfl⟩ := eP.surjective z
    exact hy w
  let c : OnePoint (K p) := (OnePoint.equivProjectivization (K p)).symm x
  obtain ⟨T, hT⟩ := dicksonWild_exists_smul_eq_infty c
  let τ : PGL p := Matrix.ProjGenLinGroup.mk T
  have hτx : τ • x = DicksonWildAffine.infinity (K p) := by
    have hc : OnePoint.equivProjectivization (K p) c = x := Equiv.apply_symm_apply _ _
    rw [← hc]
    change Matrix.ProjGenLinGroup.mk T • OnePoint.equivProjectivization (K p) c =
      OnePoint.equivProjectivization (K p) OnePoint.infty
    calc
      Matrix.ProjGenLinGroup.mk T • OnePoint.equivProjectivization (K p) c =
          OnePoint.equivProjectivization (K p) (T • c) :=
        (OnePoint.equivProjectivization_smul (g := T) c).symm
      _ = OnePoint.equivProjectivization (K p) OnePoint.infty :=
        congrArg (OnePoint.equivProjectivization (K p)) hT
  let a : MulAut (PGL p) := MulAut.conj τ
  let nToB : N →* DicksonWildAffine.borel (K p) :=
    { toFun := fun n ↦ ⟨a (n.1 : PGL p), by
        apply MulAction.mem_stabilizer_iff.mpr
        rw [← hτx]
        have hnfix : (n.1 : PGL p) • x = x :=
          (dicksonWild_mem_normalizer_iff_fixedPoint G P x hPfix hPunique n.1).mp n.2
        change (τ * (n.1 : PGL p) * τ⁻¹) • (τ • x) = τ • x
        simp only [mul_smul]
        rw [inv_smul_smul, hnfix]⟩
      map_one' := Subtype.ext (map_one a)
      map_mul' := fun n m ↦ Subtype.ext (map_mul a (n.1 : PGL p) (m.1 : PGL p)) }
  have hnToBInj : Function.Injective nToB := by
    intro n m hnm
    apply Subtype.ext
    apply G.subtype_injective
    apply a.injective
    exact congrArg (fun z : DicksonWildAffine.borel (K p) ↦ (z.1 : PGL p)) hnm
  let B : Subgroup (DicksonWildAffine.borel (K p)) := nToB.range
  let e : N ≃* B := MonoidHom.ofInjective hnToBInj
  refine ⟨a, B, e, fun n ↦ rfl, ?_⟩
  intro g hg hzero
  let A : GL (Fin 2) (K p) := DicksonWildAffine.lift (a (g : PGL p))
  have hAfix : A • (OnePoint.infty : OnePoint (K p)) = OnePoint.infty :=
    OnePoint.smul_infty_eq_self_iff.mpr hzero
  have hagfix : a (g : PGL p) • DicksonWildAffine.infinity (K p) =
      DicksonWildAffine.infinity (K p) := by
    have h := congrArg (OnePoint.equivProjectivization (K p)) hAfix
    rw [OnePoint.equivProjectivization_smul] at h
    rw [← DicksonWildAffine.mk_lift (a (g : PGL p))]
    simpa [A, DicksonWildAffine.infinity] using h
  have hconjfix : a (g : PGL p) • (τ • x) = τ • x := by
    rw [hτx]
    exact hagfix
  have hleft : τ • ((g : PGL p) • x) = τ • x := by
    calc
      τ • ((g : PGL p) • x) = a (g : PGL p) • (τ • x) := by
        change τ • ((g : PGL p) • x) =
          (τ * (g : PGL p) * τ⁻¹) • (τ • x)
        simp [mul_smul]
      _ = τ • x := hconjfix
  have hgfix : (g : PGL p) • x = x := smul_left_cancel τ hleft
  exact hg ((dicksonWild_mem_normalizer_iff_fixedPoint G P x hPfix hPunique g).mpr hgfix)

lemma dicksonWild_card_order_char_in_normalizer_coset_le
    {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
    (G : Subgroup (PGL p)) [Finite G] (hpG : p ∣ Nat.card G) (P : Sylow p G)
    (m t : ℕ) (htp : Nat.Coprime t p)
    (hNcard : Nat.card (Subgroup.normalizer (P : Set G)) = p ^ m * t)
    (g : G) (hg : g ∉ Subgroup.normalizer (P : Set G)) :
    Nat.card {n : Subgroup.normalizer (P : Set G) //
      (g * (n.1 : G)) ^ p = 1} ≤ 2 * t := by
  classical
  let N := Subgroup.normalizer (P : Set G)
  obtain ⟨a, B, e, he, hout⟩ := dicksonWild_normalizer_borel_coordinates G hpG P
  let _ : Finite B := Finite.of_surjective e e.surjective
  have hBcard : Nat.card B = p ^ m * t := by
    rw [← Nat.card_congr e.toEquiv]
    exact hNcard
  let S : GL (Fin 2) (K p) := DicksonWildAffine.lift (a (g : PGL p))
  have hS10 : (S : Matrix (Fin 2) (Fin 2) (K p)) 1 0 ≠ 0 := hout g hg
  let toParabolic : {n : N // (g * (n.1 : G)) ^ p = 1} →
      {b : B // (S * DicksonWildAffine.affineGL
        (DicksonWildAffine.gamma b.1) (DicksonWildAffine.lambda b.1)).IsParabolic} := fun n ↦
    ⟨e n.1, by
      let z : G := g * (n.1.1 : G)
      have hzNe : z ≠ 1 := by
        intro hz
        apply hg
        have hgn : g = (n.1.1 : G)⁻¹ := by
          change g * (n.1.1 : G) = 1 at hz
          exact eq_inv_of_mul_eq_one_left hz
        rw [hgn]
        exact N.inv_mem n.1.2
      have hzOrderG : orderOf z = p := orderOf_eq_prime n.2 hzNe
      have hzOrder : orderOf (z : PGL p) = p := by
        exact (orderOf_injective G.subtype G.subtype_injective z).trans hzOrderG
      have haOrder : orderOf (a (z : PGL p)) = p := by
        rw [MulEquiv.orderOf_eq]
        exact hzOrder
      have hmk : Matrix.ProjGenLinGroup.mk
          (S * DicksonWildAffine.affineGL
            (DicksonWildAffine.gamma (e n.1).1)
            (DicksonWildAffine.lambda (e n.1).1)) = a (z : PGL p) := by
        calc
          Matrix.ProjGenLinGroup.mk
              (S * DicksonWildAffine.affineGL
                (DicksonWildAffine.gamma (e n.1).1)
                (DicksonWildAffine.lambda (e n.1).1)) =
              Matrix.ProjGenLinGroup.mk S * (e n.1).1 := by
            rw [map_mul, DicksonWildAffine.mk_affineGL_gamma_lambda]
          _ = a (g : PGL p) * a (n.1.1 : PGL p) := by
            rw [DicksonWildAffine.mk_lift]
            congr 1
            exact he n.1
          _ = a (z : PGL p) := by
            exact (map_mul a (g : PGL p) (n.1.1 : PGL p)).symm
      apply dicksonWild_lift_isParabolic_of_order_eq_char
      rw [hmk]
      exact haOrder⟩
  have htoInj : Function.Injective toParabolic := by
    intro n r hnr
    apply Subtype.ext
    apply e.injective
    exact congrArg (fun z ↦ z.1) hnr
  calc
    Nat.card {n : N // (g * (n.1 : G)) ^ p = 1} ≤
        Nat.card {b : B // (S * DicksonWildAffine.affineGL
          (DicksonWildAffine.gamma b.1) (DicksonWildAffine.lambda b.1)).IsParabolic} :=
      Nat.card_le_card_of_injective toParabolic htoInj
    _ ≤ 2 * Nat.card (SemidirectProduct.rightHom.comp
        (DicksonWildAffine.toAff.comp B.subtype)).range :=
      DicksonWildAffine.card_parabolic_borel_le_twice_range S hS10 B
    _ = 2 * t := by
      rw [dicksonWild_borel_multiplier_range_card B m t htp hBcard]

lemma dicksonWild_sandwich_bound
    {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
    (G : Subgroup (PGL p)) [Finite G] (hpG : p ∣ Nat.card G) (P : Sylow p G)
    (m f t : ℕ) (hf : 0 < f) (htp : Nat.Coprime t p)
    (hPcard : Nat.card (P : Subgroup G) = p ^ m)
    (hNcard : Nat.card (Subgroup.normalizer (P : Set G)) = p ^ m * t)
    (hindex : (Subgroup.normalizer (P : Set G)).index = 1 + f * p ^ m)
    (hcount : Nat.card {g : G // g ≠ 1 ∧ g ^ p = 1} =
      (1 + f * p ^ m) * (p ^ m - 1)) :
    p ^ m - 1 ≤ 2 * t := by
  classical
  let N := Subgroup.normalizer (P : Set G)
  let O := {g : G // g ∉ N ∧ g ^ p = 1}
  let Q := G ⧸ N
  let q1 : Q := Quotient.mk'' (1 : G)
  let C := {q : Q // q ≠ q1}
  let coset : O → C := fun g ↦ ⟨Quotient.mk'' g.1, by
    intro hq
    have hrel : QuotientGroup.leftRel N g.1 1 := Quotient.exact hq
    have hginv : g.1⁻¹ ∈ N := by
      simpa using QuotientGroup.leftRel_apply.mp hrel
    exact g.2.1 (by simpa using N.inv_mem hginv)⟩
  have hfiber (c : C) : Nat.card {g : O // coset g = c} ≤ 2 * t := by
    let s : G := c.1.out
    have hsClass : Quotient.mk'' s = c.1 := Quotient.out_eq c.1
    have hs : s ∉ N := by
      intro hsN
      apply c.2
      rw [← hsClass]
      apply Quotient.sound
      apply QuotientGroup.leftRel_apply.mpr
      simpa using N.inv_mem hsN
    let toN : {g : O // coset g = c} →
        {n : N // (s * (n.1 : G)) ^ p = 1} := fun g ↦
      ⟨⟨s⁻¹ * g.1.1, by
        apply QuotientGroup.leftRel_apply.mp
        apply Quotient.exact
        exact hsClass.trans (congrArg (fun z : C ↦ z.1) g.2).symm⟩, by
        simpa [mul_assoc] using g.1.2.2⟩
    have htoN : Function.Injective toN := by
      intro g h hgh
      apply Subtype.ext
      apply Subtype.ext
      have hv := congrArg (fun z : {n : N // (s * (n.1 : G)) ^ p = 1} ↦
        (z.1 : G)) hgh
      change s⁻¹ * g.1.1 = s⁻¹ * h.1.1 at hv
      exact mul_left_cancel hv
    exact (Nat.card_le_card_of_injective toN htoN).trans
      (dicksonWild_card_order_char_in_normalizer_coset_le
        G hpG P m t htp hNcard s hs)
  have hupper : Nat.card O ≤ 2 * t * Nat.card C :=
    DicksonWildAffine.card_le_mul_card_of_fiber_le coset (2 * t) hfiber
  have hOcard : Nat.card O = f * p ^ m * (p ^ m - 1) :=
    dicksonWild_card_order_char_outside_normalizer G P m f hPcard hcount
  have hCcard : Nat.card C = f * p ^ m := by
    let _ : Fintype Q := Fintype.ofFinite Q
    let _ : Fintype C := Fintype.ofFinite C
    rw [Nat.card_eq_fintype_card]
    calc
      Fintype.card C = Fintype.card Q - 1 :=
        Fintype.card_subtype_compl (fun q : Q ↦ q = q1) |>.trans (by simp)
      _ = N.index - 1 := by
        rw [Subgroup.index_eq_card]
        exact congrArg (fun n ↦ n - 1) Nat.card_eq_fintype_card.symm
      _ = f * p ^ m := by rw [hindex]; omega
  rw [hOcard, hCcard] at hupper
  apply Nat.le_of_mul_le_mul_left (c := f * p ^ m)
  · simpa [mul_assoc, mul_left_comm, mul_comm] using hupper
  · exact mul_pos hf (pow_pos (Fact.out : p.Prime).pos m)

lemma dicksonWild_card_order_char_in_normalizer_coset_eq
    {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
    (G : Subgroup (PGL p)) [Finite G] (hpG : p ∣ Nat.card G) (P : Sylow p G)
    (m f t : ℕ) (htp : Nat.Coprime t p)
    (hPcard : Nat.card (P : Subgroup G) = p ^ m)
    (hNcard : Nat.card (Subgroup.normalizer (P : Set G)) = p ^ m * t)
    (hindex : (Subgroup.normalizer (P : Set G)).index = 1 + f * p ^ m)
    (hcount : Nat.card {g : G // g ≠ 1 ∧ g ^ p = 1} =
      (1 + f * p ^ m) * (p ^ m - 1))
    (hhalf : 2 * t = p ^ m - 1)
    (g : G) (hg : g ∉ Subgroup.normalizer (P : Set G)) :
    Nat.card {n : Subgroup.normalizer (P : Set G) //
      (g * (n.1 : G)) ^ p = 1} = 2 * t := by
  classical
  let N := Subgroup.normalizer (P : Set G)
  let O := {z : G // z ∉ N ∧ z ^ p = 1}
  let Q := G ⧸ N
  let q1 : Q := Quotient.mk'' (1 : G)
  let C := {q : Q // q ≠ q1}
  let coset : O → C := fun z ↦ ⟨Quotient.mk'' z.1, by
    intro hq
    have hrel : QuotientGroup.leftRel N z.1 1 := Quotient.exact hq
    have hzinv : z.1⁻¹ ∈ N := by
      simpa using QuotientGroup.leftRel_apply.mp hrel
    exact z.2.1 (by simpa using N.inv_mem hzinv)⟩
  have hfiber (c : C) : Nat.card {z : O // coset z = c} ≤ 2 * t := by
    let s : G := c.1.out
    have hsClass : Quotient.mk'' s = c.1 := Quotient.out_eq c.1
    have hs : s ∉ N := by
      intro hsN
      apply c.2
      rw [← hsClass]
      apply Quotient.sound
      apply QuotientGroup.leftRel_apply.mpr
      simpa using N.inv_mem hsN
    let toN : {z : O // coset z = c} →
        {n : N // (s * (n.1 : G)) ^ p = 1} := fun z ↦
      ⟨⟨s⁻¹ * z.1.1, by
        apply QuotientGroup.leftRel_apply.mp
        apply Quotient.exact
        exact hsClass.trans (congrArg (fun w : C ↦ w.1) z.2).symm⟩, by
        simpa [mul_assoc] using z.1.2.2⟩
    have htoN : Function.Injective toN := by
      intro z w hzw
      apply Subtype.ext
      apply Subtype.ext
      have hv := congrArg
        (fun n : {n : N // (s * (n.1 : G)) ^ p = 1} ↦ (n.1 : G)) hzw
      change s⁻¹ * z.1.1 = s⁻¹ * w.1.1 at hv
      exact mul_left_cancel hv
    exact (Nat.card_le_card_of_injective toN htoN).trans
      (dicksonWild_card_order_char_in_normalizer_coset_le
        G hpG P m t htp hNcard s hs)
  have hOcard : Nat.card O = f * p ^ m * (p ^ m - 1) :=
    dicksonWild_card_order_char_outside_normalizer G P m f hPcard hcount
  have hCcard : Nat.card C = f * p ^ m := by
    let _ : Fintype Q := Fintype.ofFinite Q
    let _ : Fintype C := Fintype.ofFinite C
    rw [Nat.card_eq_fintype_card]
    calc
      Fintype.card C = Fintype.card Q - 1 :=
        Fintype.card_subtype_compl (fun q : Q ↦ q = q1) |>.trans (by simp)
      _ = N.index - 1 := by
        rw [Subgroup.index_eq_card]
        exact congrArg (fun n ↦ n - 1) Nat.card_eq_fintype_card.symm
      _ = f * p ^ m := by rw [hindex]; omega
  have htotal : Nat.card O = 2 * t * Nat.card C := by
    rw [hOcard, hCcard, hhalf]
    ring
  have hfiberEq : ∀ c : C, Nat.card {z : O // coset z = c} = 2 * t :=
    DicksonWildAffine.card_fiber_eq_of_le_of_card_eq_mul coset (2 * t) hfiber htotal
  let cg : C := ⟨Quotient.mk'' g, by
    intro hq
    have hrel : QuotientGroup.leftRel N g 1 := Quotient.exact hq
    have hginv : g⁻¹ ∈ N := by simpa using QuotientGroup.leftRel_apply.mp hrel
    exact hg (by simpa using N.inv_mem hginv)⟩
  let toN : {z : O // coset z = cg} →
      {n : N // (g * (n.1 : G)) ^ p = 1} := fun z ↦
    ⟨⟨g⁻¹ * z.1.1, by
      apply QuotientGroup.leftRel_apply.mp
      apply Quotient.exact
      exact congrArg (fun w : C ↦ w.1) z.2 |>.symm⟩, by
      simpa [mul_assoc] using z.1.2.2⟩
  have htoN : Function.Injective toN := by
    intro z w hzw
    apply Subtype.ext
    apply Subtype.ext
    have hv := congrArg
      (fun n : {n : N // (g * (n.1 : G)) ^ p = 1} ↦ (n.1 : G)) hzw
    change g⁻¹ * z.1.1 = g⁻¹ * w.1.1 at hv
    exact mul_left_cancel hv
  have hlower : 2 * t ≤ Nat.card {n : N // (g * (n.1 : G)) ^ p = 1} := by
    rw [← hfiberEq cg]
    exact Nat.card_le_card_of_injective toN htoN
  exact Nat.le_antisymm
    (dicksonWild_card_order_char_in_normalizer_coset_le
      G hpG P m t htp hNcard g hg) hlower

lemma dicksonWild_exists_matrix_normal_form
    {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
    (G : Subgroup (PGL p)) [Finite G] (hpG : p ∣ Nat.card G) (P : Sylow p G)
    (m t : ℕ) (hm : 1 ≤ m) (htp : Nat.Coprime t p)
    (hNcard : Nat.card (Subgroup.normalizer (P : Set G)) = p ^ m * t)
    (hsandwich : p ^ m - 1 ≤ 2 * t) :
    ∃ (M : Subfield (K p)) (L : Subgroup Mˣ) (j : G →* PGL p)
      (coord : Subgroup.normalizer (P : Set G) → M × L),
      Finite M ∧ Nat.card M = p ^ m ∧ Nat.card L = t ∧
      Function.Injective j ∧ Function.Bijective coord ∧
      (∀ n : Subgroup.normalizer (P : Set G),
        j n.1 = Matrix.ProjGenLinGroup.map M.subtype
          (Matrix.ProjGenLinGroup.mk
            (DicksonWildAffine.affineGL (coord n).1 (coord n).2.1))) ∧
      ∀ g : G, g ∉ Subgroup.normalizer (P : Set G) →
        ∃ S : GL (Fin 2) (K p), Matrix.ProjGenLinGroup.mk S = j g ∧
          (S : Matrix (Fin 2) (Fin 2) (K p)) 1 0 ≠ 0 := by
  classical
  let N := Subgroup.normalizer (P : Set G)
  obtain ⟨a, B, e, he, hout⟩ := dicksonWild_normalizer_borel_coordinates G hpG P
  let _ : Finite B := Finite.of_surjective e e.surjective
  let H : Subgroup (DicksonWildAffine.Aff (K p)) := Subgroup.map
    DicksonWildAffine.borelMulEquivAffine.toMonoidHom B
  let eH : B ≃* H := DicksonWildAffine.borelMulEquivAffine.subgroupMap B
  let _ : Finite H := Finite.of_surjective eH eH.surjective
  have hHcard : Nat.card H = p ^ m * t := by
    rw [← Nat.card_congr eH.toEquiv, ← Nat.card_congr e.toEquiv]
    exact hNcard
  have hrange : Nat.card (DicksonWildAffine.rightRestrict H).range = t :=
    dicksonWild_affine_right_range_card H m t htp hHcard
  obtain ⟨M, c, L, coordH, hMfinite, hMcard, hLcard, hcoordH, hlower, hmatrix⟩ :=
    DicksonWildAffine.exists_affine_matrix_normal_form H m t hm hHcard hrange hsandwich
  let κ : PGL p := Matrix.ProjGenLinGroup.mk c
  let j : G →* PGL p :=
    (MulAut.conj κ).toMonoidHom.comp (a.toMonoidHom.comp G.subtype)
  let coord : N → M × L := fun n ↦ coordH (eH (e n))
  have hj : Function.Injective j :=
    (MulAut.conj κ).injective.comp (a.injective.comp G.subtype_injective)
  have hcoord : Function.Bijective coord :=
    hcoordH.comp (eH.bijective.comp e.bijective)
  refine ⟨M, L, j, coord, hMfinite, hMcard, hLcard, hj, hcoord, ?_, ?_⟩
  · intro n
    let b : B := e n
    let h : H := eH b
    have hmat := hmatrix h
    have hb : (b.1 : PGL p) = Matrix.ProjGenLinGroup.mk
        (DicksonWildAffine.affineGL h.1.left.toAdd h.1.right) := by
      calc
        (b.1 : PGL p) = Matrix.ProjGenLinGroup.mk
            (DicksonWildAffine.affineGL (DicksonWildAffine.gamma b.1)
              (DicksonWildAffine.lambda b.1)) :=
          (DicksonWildAffine.mk_affineGL_gamma_lambda b.1).symm
        _ = Matrix.ProjGenLinGroup.mk
            (DicksonWildAffine.affineGL h.1.left.toAdd h.1.right) := by rfl
    calc
      j n.1 = κ * a (n.1 : PGL p) * κ⁻¹ := rfl
      _ = Matrix.ProjGenLinGroup.mk c * b.1 *
          (Matrix.ProjGenLinGroup.mk c)⁻¹ := by rw [he n]
      _ = Matrix.ProjGenLinGroup.mk
          (c * DicksonWildAffine.affineGL h.1.left.toAdd h.1.right * c⁻¹) := by
        simp only [map_mul, map_inv]
        rw [hb]
      _ = Matrix.ProjGenLinGroup.mk
          (Matrix.GeneralLinearGroup.map M.subtype
            (DicksonWildAffine.affineGL (coord n).1 (coord n).2.1)) := by
        exact congrArg Matrix.ProjGenLinGroup.mk hmat
      _ = Matrix.ProjGenLinGroup.map M.subtype
          (Matrix.ProjGenLinGroup.mk
            (DicksonWildAffine.affineGL (coord n).1 (coord n).2.1)) := by
        rw [Matrix.ProjGenLinGroup.map_mk]
  · intro g hg
    let A : GL (Fin 2) (K p) := DicksonWildAffine.lift (a (g : PGL p))
    let S : GL (Fin 2) (K p) := c * A * c⁻¹
    refine ⟨S, ?_, hlower A (hout g hg)⟩
    calc
      Matrix.ProjGenLinGroup.mk S = Matrix.ProjGenLinGroup.mk c *
          Matrix.ProjGenLinGroup.mk A * (Matrix.ProjGenLinGroup.mk c)⁻¹ := by
        simp [S]
      _ = κ * a (g : PGL p) * κ⁻¹ := by
        rw [DicksonWildAffine.mk_lift]
      _ = j g := rfl

end Dickson
end MetaMathlibExt
