import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma section_eq_of_forall_not_mem
  {X : (Scheme : Type (u + 1))} (W : X.Opens) (hW : ∀ x : X, x ∉ W)
  (s t : X.presheaf.obj (op W)) : s = t :=
  TopCat.Presheaf.section_ext X.sheaf W s t (fun x hx => absurd hx (hW x))
private lemma exists_isIdempotentElem_of_isClopen
  {X : (Scheme : Type (u + 1))} {U : Set X} (hU : IsClopen U) :
    ∃ e : X.presheaf.obj (op ⊤), IsIdempotentElem e ∧ (∀ x : X, x ∈ U → X.presheaf.germ ⊤ x trivial e = 1) ∧ (∀ x : X, x ∉ U → X.presheaf.germ ⊤ x trivial e = 0) := by
  let U' : X.Opens := ⟨U, hU.isOpen⟩
  let V' : X.Opens := ⟨Uᶜ, hU.compl.isOpen⟩
  have hUV : ∀ x : X, x ∉ U' ⊓ V' := by
    intro x hx
    apply hx.2 hx.1
  have htop : (⊤ : X.Opens) ≤ U' ⊔ V' := by
    intro x _
    if hx : x ∈ U then
      apply Or.inl hx
    else
      apply Or.inr hx
  let p : RingHom.eqLocus
    (RingHom.comp (X.sheaf.obj.map (homOfLE inf_le_left : U' ⊓ V' ⟶ U').op).hom
      (RingHom.fst (X.sheaf.obj.obj <| op U') (X.sheaf.obj.obj <| op V')))
    (RingHom.comp (X.sheaf.obj.map (homOfLE inf_le_right : U' ⊓ V' ⟶ V').op).hom
      (RingHom.snd (X.sheaf.obj.obj <| op U') (X.sheaf.obj.obj <| op V'))) :=
    ⟨(1, 0), section_eq_of_forall_not_mem (U' ⊓ V') hUV _ _⟩
  let s : X.presheaf.obj (op (U' ⊔ V')) := (X.sheaf.objSupIsoProdEqLocus U' V').inv p
  have hsU : X.presheaf.map (homOfLE (le_sup_left : U' ≤ U' ⊔ V')).op s = 1 :=
    TopCat.Sheaf.objSupIsoProdEqLocus_inv_fst X.sheaf U' V' p
  have hsV : X.presheaf.map (homOfLE (le_sup_right : V' ≤ U' ⊔ V')).op s = 0 :=
    TopCat.Sheaf.objSupIsoProdEqLocus_inv_snd X.sheaf U' V' p
  let e : X.presheaf.obj (op ⊤) := X.presheaf.map (homOfLE htop).op s
  have he1 : ∀ x : X, x ∈ U → X.presheaf.germ ⊤ x trivial e = 1 := by
    intro x hx
    have h1 := TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE htop) x trivial s
    have h2 := TopCat.Presheaf.germ_res_apply X.presheaf
      (homOfLE (le_sup_left : U' ≤ U' ⊔ V')) x (show x ∈ U' from hx) s
    rw [hsU, map_one] at h2
    simp only [e]
    rw [h1, ← h2]
  have he0 : ∀ x : X, x ∉ U → X.presheaf.germ ⊤ x trivial e = 0 := by
    intro x hx
    have h1 := TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE htop) x trivial s
    have h2 := TopCat.Presheaf.germ_res_apply X.presheaf
      (homOfLE (le_sup_right : V' ≤ U' ⊔ V')) x (show x ∈ V' from hx) s
    rw [hsV, map_zero] at h2
    simp only [e]
    rw [h1, ← h2]
  refine ⟨e, ?_, he1, he0⟩
  show e * e = e
  apply TopCat.Presheaf.section_ext X.sheaf ⊤ (e * e) e
  intro x hx
  have hm : X.presheaf.germ ⊤ x hx (e * e) =
    X.presheaf.germ ⊤ x hx e * X.presheaf.germ ⊤ x hx e := map_mul _ _ _
  change X.presheaf.germ ⊤ x hx (e * e) = X.presheaf.germ ⊤ x hx e
  rw [hm]
  if hxU : x ∈ U then
    rw [he1 x hxU, mul_one]
  else
    rw [he0 x hxU, mul_zero]
private lemma germ_one_ne_zero
  {X : (Scheme : Type (u + 1))} (x : X) :
    X.presheaf.germ ⊤ x trivial (1 : X.presheaf.obj (op ⊤)) ≠ X.presheaf.germ ⊤ x trivial 0 := by
  rw [map_one, map_zero]
  apply one_ne_zero
/--
[AlgebraicGeometry_Scheme_connectedSpace_of_forall_isIdempotentElem](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_connectedSpace_of_forall_isIdempotentElem.lean)
-/
@[path]
private lemma main
  (X : (Scheme : Type (u + 1))) [Nonempty X]
  (h : ∀ e : X.presheaf.obj (op ⊤), IsIdempotentElem e → e = 0 ∨ e = 1) :
    ConnectedSpace X := by
  have hpre : PreconnectedSpace X := by
    rw [preconnectedSpace_iff_clopen]
    intro U hU
    obtain ⟨e, he, he1, he0⟩ := exists_isIdempotentElem_of_isClopen hU
    obtain h0 | h1 := h e he
    ·
      left
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have := he1 x hx
      rw [h0, map_zero] at this
      apply zero_ne_one this
    ·
      right
      apply Set.eq_univ_iff_forall.mpr
      intro x
      by_contra hx
      have := he0 x hx
      rw [h1, map_one] at this
      apply one_ne_zero this
  let _ := hpre
  exact ⟨inferInstance⟩


-- created on 2026-10-20
