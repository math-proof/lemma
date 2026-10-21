import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

variable {X : (Scheme : Type (u + 1))} [IsIntegral X] (M : X.Modules)
private lemma map_ne_zero_aux
  (φ : ∀ U : X.Opens, (M.presheaf.obj (op U)) →+ (X.functionField : Type u))
  (hnat : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V → ∀ m : (M.presheaf.obj (op U)), φ V (M.presheaf.map (homOfLE h).op m) = φ U m)
    (hinj : ∀ U : X.Opens, Nonempty U → Function.Injective (φ U))
    {U V : X.Opens} (h : V ≤ U) [hV : Nonempty V] {m : (M.presheaf.obj (op U))} (hm : m ≠ 0) :
    M.presheaf.map (homOfLE h).op m ≠ 0 := by
  let _ : Nonempty U := by
    obtain ⟨⟨z, hz⟩⟩ := hV
    exact ⟨⟨z, h hz⟩⟩
  intro h0
  apply hm
  apply hinj U inferInstance
  rw [map_zero, ← hnat U V h hV m, h0, map_zero]
private lemma ratio_eq_of_affine
  (φ φ' : ∀ U : X.Opens, (M.presheaf.obj (op U)) →+ (X.functionField : Type u))
  (hsmul : ∀ (U : X.Opens) [Nonempty U] (a : (X.presheaf.obj (op U))) (m : (M.presheaf.obj (op U))), φ U (a • m) = algebraMap (X.presheaf.obj (op U)) X.functionField a * φ U m)
    (hsmul' : ∀ (U : X.Opens) [Nonempty U] (a : (X.presheaf.obj (op U))) (m : (M.presheaf.obj (op U))), φ' U (a • m) = algebraMap (X.presheaf.obj (op U)) X.functionField a * φ' U m)
    (hinj : ∀ U : X.Opens, Nonempty U → Function.Injective (φ U))
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] (m₁ m₂ : (M.presheaf.obj (op U))) (h₁ : m₁ ≠ 0) (h₂ : m₂ ≠ 0) :
    φ' U m₁ / φ U m₁ = φ' U m₂ / φ U m₂ := by
  let _ := functionField_isFractionRing_of_isAffineOpen X U hU
  have hφ₁ : φ U m₁ ≠ 0 := fun h => h₁ (hinj U inferInstance (h.trans (map_zero _).symm))
  have hφ₂ : φ U m₂ ≠ 0 := fun h => h₂ (hinj U inferInstance (h.trans (map_zero _).symm))
  obtain ⟨a', a, ha, hq⟩ := IsFractionRing.div_surjective (A := (X.presheaf.obj (op U))) (φ U m₁ / φ U m₂)
  have ha0 : algebraMap (X.presheaf.obj (op U)) X.functionField a ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ha
  have hrel : algebraMap (X.presheaf.obj (op U)) X.functionField a * φ U m₁ = algebraMap (X.presheaf.obj (op U)) X.functionField a' * φ U m₂ := by
    rw [div_eq_div_iff ha0 hφ₂] at hq
    calc
      _ = φ U m₁ * algebraMap (X.presheaf.obj (op U)) X.functionField a := mul_comm _ _
      _ = algebraMap (X.presheaf.obj (op U)) X.functionField a' * φ U m₂ := hq.symm
  have hsec : a • m₁ = a' • m₂ := by
    apply hinj U inferInstance
    rw [hsmul, hsmul, hrel]
  have hrel' : algebraMap (X.presheaf.obj (op U)) X.functionField a * φ' U m₁ = algebraMap (X.presheaf.obj (op U)) X.functionField a' * φ' U m₂ := by
    rw [← hsmul', ← hsmul', hsec]
  have ha'0 : algebraMap (X.presheaf.obj (op U)) X.functionField a' ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hrel
    apply (mul_ne_zero ha0 hφ₁) hrel
  rw [div_eq_div_iff hφ₁ hφ₂]
  have e1 := congrArg (· * (φ' U m₁ * φ U m₂)) hrel
  have e2 := congrArg (· * (φ U m₁ * φ U m₂)) hrel'
  have e3 : algebraMap (X.presheaf.obj (op U)) X.functionField a' * φ U m₂ * (φ' U m₁ * φ U m₂) =
      algebraMap (X.presheaf.obj (op U)) X.functionField a' * φ' U m₂ * (φ U m₁ * φ U m₂) := by
    rw [← e1, ← e2]
    ring
  apply mul_right_cancel₀ (mul_ne_zero ha'0 hφ₂)
  calc
    _ = algebraMap (X.presheaf.obj (op U)) X.functionField a' * φ U m₂ * (φ' U m₁ * φ U m₂) := by ring
    _ = algebraMap (X.presheaf.obj (op U)) X.functionField a' * φ' U m₂ * (φ U m₁ * φ U m₂) := e3
    _ = φ' U m₂ * φ U m₁ * (algebraMap (X.presheaf.obj (op U)) X.functionField a' * φ U m₂) := by ring
variable (φ φ' : ∀ U : X.Opens, (M.presheaf.obj (op U)) →+ (X.functionField : Type u))
variable (hnat : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V → ∀ m : (M.presheaf.obj (op U)), φ V (M.presheaf.map (homOfLE h).op m) = φ U m)
variable (hnat' : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V → ∀ m : (M.presheaf.obj (op U)), φ' V (M.presheaf.map (homOfLE h).op m) = φ' U m)
variable (hsmul : ∀ (U : X.Opens) [Nonempty U] (a : (X.presheaf.obj (op U))) (m : (M.presheaf.obj (op U))), φ U (a • m) = algebraMap (X.presheaf.obj (op U)) X.functionField a * φ U m)
variable (hsmul' : ∀ (U : X.Opens) [Nonempty U] (a : (X.presheaf.obj (op U))) (m : (M.presheaf.obj (op U))), φ' U (a • m) = algebraMap (X.presheaf.obj (op U)) X.functionField a * φ' U m)
variable (hinj : ∀ U : X.Opens, Nonempty U → Function.Injective (φ U))
variable (hinj' : ∀ U : X.Opens, Nonempty U → Function.Injective (φ' U))
private lemma ratio_eq
  (hnat : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V → ∀ m : (M.presheaf.obj (op U)),
    φ V (M.presheaf.map (homOfLE h).op m) = φ U m)
  (hnat' : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V → ∀ m : (M.presheaf.obj (op U)),
    φ' V (M.presheaf.map (homOfLE h).op m) = φ' U m)
  (hsmul : ∀ (U : X.Opens) [Nonempty U] (a : (X.presheaf.obj (op U))) (m : (M.presheaf.obj (op U))),
    φ U (a • m) = algebraMap (X.presheaf.obj (op U)) X.functionField a * φ U m)
  (hsmul' : ∀ (U : X.Opens) [Nonempty U] (a : (X.presheaf.obj (op U))) (m : (M.presheaf.obj (op U))),
    φ' U (a • m) = algebraMap (X.presheaf.obj (op U)) X.functionField a * φ' U m)
  (hinj : ∀ U : X.Opens, Nonempty U → Function.Injective (φ U))
  (U₁ U₂ : X.Opens) [Nonempty U₁] [Nonempty U₂] (m₁ : (M.presheaf.obj (op U₁))) (m₂ : (M.presheaf.obj (op U₂)))
    (h₁ : m₁ ≠ 0) (h₂ : m₂ ≠ 0) :
    φ' U₁ m₁ / φ U₁ m₁ = φ' U₂ m₂ / φ U₂ m₂ := by
  obtain ⟨⟨u, hu⟩⟩ := (inferInstance : Nonempty U₁)
  obtain ⟨⟨w, hw⟩⟩ := (inferInstance : Nonempty U₂)
  obtain ⟨z, hz⟩ := nonempty_preirreducible_inter U₁.isOpen U₂.isOpen ⟨u, hu⟩ ⟨w, hw⟩
  obtain ⟨W, hWaff, hzW, hW⟩ :=
    (Iff.mp Opens.isBasis_iff_nbhd X.isBasis_affineOpens) (show z ∈ U₁ ⊓ U₂ from hz)
  let _ : Nonempty W := ⟨⟨z, hzW⟩⟩
  have hW₁ : W ≤ U₁ := hW.trans inf_le_left
  have hW₂ : W ≤ U₂ := hW.trans inf_le_right
  have hr₁ := map_ne_zero_aux M φ hnat hinj hW₁ h₁
  have hr₂ := map_ne_zero_aux M φ hnat hinj hW₂ h₂
  rw [← hnat U₁ W hW₁ inferInstance m₁, ← hnat' U₁ W hW₁ inferInstance m₁,
    ← hnat U₂ W hW₂ inferInstance m₂, ← hnat' U₂ W hW₂ inferInstance m₂]
  apply ratio_eq_of_affine M φ φ' hsmul hsmul' hinj W hWaff _ _ hr₁ hr₂
private lemma exists_eq_mul
  (hnat : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V → ∀ m : (M.presheaf.obj (op U)),
    φ V (M.presheaf.map (homOfLE h).op m) = φ U m)
  (hnat' : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V → ∀ m : (M.presheaf.obj (op U)),
    φ' V (M.presheaf.map (homOfLE h).op m) = φ' U m)
  (hsmul : ∀ (U : X.Opens) [Nonempty U] (a : (X.presheaf.obj (op U))) (m : (M.presheaf.obj (op U))),
    φ U (a • m) = algebraMap (X.presheaf.obj (op U)) X.functionField a * φ U m)
  (hsmul' : ∀ (U : X.Opens) [Nonempty U] (a : (X.presheaf.obj (op U))) (m : (M.presheaf.obj (op U))),
    φ' U (a • m) = algebraMap (X.presheaf.obj (op U)) X.functionField a * φ' U m)
  (hinj : ∀ U : X.Opens, Nonempty U → Function.Injective (φ U))
  (hinj' : ∀ U : X.Opens, Nonempty U → Function.Injective (φ' U))
  (U₀ : X.Opens) [Nonempty U₀] (m₀ : (M.presheaf.obj (op U₀))) (hm₀ : m₀ ≠ 0) :
    ∃ g : X.functionField, g ≠ 0 ∧ ∀ (U : X.Opens) [Nonempty U] (m : (M.presheaf.obj (op U))), φ' U m = g * φ U m := by
  refine ⟨φ' U₀ m₀ / φ U₀ m₀, ?_, ?_⟩
  ·
    apply div_ne_zero
      (fun h => hm₀ (hinj' U₀ inferInstance (h.trans (map_zero _).symm)))
      (fun h => hm₀ (hinj U₀ inferInstance (h.trans (map_zero _).symm)))
  ·
    intro U _ m
    if hm : m = 0 then
      rw [hm, map_zero, map_zero, mul_zero]
    else
      have hφ : φ U m ≠ 0 := fun h => hm (hinj U inferInstance (h.trans (map_zero _).symm))
      rw [ratio_eq M φ φ' hnat hnat' hsmul hsmul' hinj U₀ U m₀ m hm₀ hm, div_mul_cancel₀ _ hφ]
private lemma AlgebraicGeometry.Scheme.Modules.exists_forall_eq_mul_of_presentations'
  {X : (Scheme : Type (u + 1))} [IsIntegral X] (M : X.Modules)
    (φ φ' : ∀ U : X.Opens, (M.presheaf.obj (op U)) →+ (X.functionField : Type u))
    (hnat : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : (M.presheaf.obj (op U)), φ V (M.presheaf.map (homOfLE h).op m) = φ U m)
    (hnat' : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : (M.presheaf.obj (op U)), φ' V (M.presheaf.map (homOfLE h).op m) = φ' U m)
    (hsmul : ∀ (U : X.Opens) [Nonempty U] (a : (X.presheaf.obj (op U))) (m : (M.presheaf.obj (op U))), φ U (a • m) = algebraMap (X.presheaf.obj (op U)) X.functionField a * φ U m)
    (hsmul' : ∀ (U : X.Opens) [Nonempty U] (a : (X.presheaf.obj (op U))) (m : (M.presheaf.obj (op U))), φ' U (a • m) = algebraMap (X.presheaf.obj (op U)) X.functionField a * φ' U m)
    (hinj : ∀ U : X.Opens, Nonempty U → Function.Injective (φ U))
    (hinj' : ∀ U : X.Opens, Nonempty U → Function.Injective (φ' U))
    (hsec : ∃ (U : X.Opens) (m : (M.presheaf.obj (op U))), m ≠ 0) :
    ∃ g : X.functionField, g ≠ 0 ∧ ∀ (U : X.Opens) [Nonempty U] (m : (M.presheaf.obj (op U))), φ' U m = g * φ U m := by
  obtain ⟨U₀, m₀, hm₀⟩ := hsec
  if hU₀ : Nonempty U₀ then
    apply exists_eq_mul M φ φ' hnat hnat' hsmul hsmul' hinj hinj' U₀ m₀ hm₀
  else
    exfalso
    apply hm₀
    have hbot : U₀ = ⊥ := by
      ext z
      simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hz => hU₀ ⟨⟨z, hz⟩⟩
    subst hbot
    let F : TopCat.Sheaf Ab X := ⟨M.presheaf, M.isSheaf⟩
    refine TopCat.Sheaf.eq_of_locally_eq' F (fun i : Empty => (⊥ : X.Opens)) ⊥ (fun i => i.elim) ?_ m₀ 0
      (fun i => i.elim)
    intro z hz
    apply hz.elim
/--
[AlgebraicGeometry_Scheme_Modules_exists_forall_eq_mul_of_presentations](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_exists_forall_eq_mul_of_presentations.lean)
-/
@[path]
private lemma main
  {X : (Scheme : Type (u + 1))} [IsIntegral X] (M : X.Modules)
    (φ φ' : ∀ U : X.Opens, (M.presheaf.obj (op U)) →+ (X.functionField : Type u))
    (hnat : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : (M.presheaf.obj (op U)), φ V (M.presheaf.map (homOfLE h).op m) = φ U m)
    (hnat' : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : (M.presheaf.obj (op U)), φ' V (M.presheaf.map (homOfLE h).op m) = φ' U m)
    (hsmul : ∀ (U : X.Opens) [Nonempty U] (a : (X.presheaf.obj (op U))) (m : (M.presheaf.obj (op U))), φ U (a • m) = algebraMap (X.presheaf.obj (op U)) X.functionField a * φ U m)
    (hsmul' : ∀ (U : X.Opens) [Nonempty U] (a : (X.presheaf.obj (op U))) (m : (M.presheaf.obj (op U))), φ' U (a • m) = algebraMap (X.presheaf.obj (op U)) X.functionField a * φ' U m)
    (hinj : ∀ U : X.Opens, Nonempty U → Function.Injective (φ U))
    (hinj' : ∀ U : X.Opens, Nonempty U → Function.Injective (φ' U))
    (hsec : ∃ (U : X.Opens) (m : (M.presheaf.obj (op U))), m ≠ 0) :
    ∃ g : X.functionField, g ≠ 0 ∧ ∀ (U : X.Opens) [Nonempty U] (m : (M.presheaf.obj (op U))), φ' U m = g * φ U m :=
  AlgebraicGeometry.Scheme.Modules.exists_forall_eq_mul_of_presentations' M φ φ' hnat hnat' hsmul hsmul' hinj hinj' hsec


-- created on 2026-10-20
