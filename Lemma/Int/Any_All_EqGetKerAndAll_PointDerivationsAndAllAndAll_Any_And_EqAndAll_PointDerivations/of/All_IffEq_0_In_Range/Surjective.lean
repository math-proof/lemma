import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Algebra.PointDerivations.Part2
import Def.Algebra_PointDerivations
open scoped TensorProduct
set_option maxHeartbeats 1000000

/--
[Algebra_PointDerivations_exists_reader_tensor_linearMap_dual_of_linearEquiv_tensor](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_PointDerivations_exists_reader_tensor_linearMap_dual_of_linearEquiv_tensor.lean)
-/
@[path]
private lemma main
  {κ : Type} [Field κ]
  {R : Type} [CommRing R] [Algebra κ R]
  {W : Type} [AddCommGroup W] [Module κ W]
  {ev : R →+* κ}
  {Φ : ∀ (M : Type) [AddCommGroup M] [Module κ M],
    ↥(Algebra.PointDerivations κ R ev M) ≃ₗ[κ] (W ⊗[κ] M)}
-- given
  (hΦnat : ∀ (M M' : Type) [AddCommGroup M] [Module κ M] [AddCommGroup M'] [Module κ M'] (g : M →ₗ[κ] M') (δ : ↥(Algebra.PointDerivations κ R ev M)),
    Φ M' (Algebra.PointDerivations.map ev g δ) =
      TensorProduct.map (LinearMap.id : W →ₗ[κ] W) g (Φ M δ))
  {C₀ C₁ C₂ : Type} [AddCommGroup C₀] [Module κ C₀] [AddCommGroup C₁] [Module κ C₁]
  [AddCommGroup C₂] [Module κ C₂]
  {d₀ : C₀ →ₗ[κ] C₁} {d₁ : C₁ →ₗ[κ] C₂}
  {H₁ : Type} [AddCommGroup H₁] [Module κ H₁]
  {cls₁ : ↥(LinearMap.ker d₁) →ₗ[κ] H₁}
  (hcls₁ : Function.Surjective cls₁)
  (hcls₁0 : ∀ z : ↥(LinearMap.ker d₁), cls₁ z = 0 ↔ (z : C₁) ∈ LinearMap.range d₀)
  {V : Type} [AddCommGroup V] [Module κ V] [Module.Finite κ V] :
-- imply
  ∃ Ψ : ↥(Algebra.PointDerivations κ R ev (Module.Dual κ V →ₗ[κ] C₁)) →
      W ⊗[κ] (Module.Dual κ V →ₗ[κ] H₁),
    (∀ c : ↥(Algebra.PointDerivations κ R ev (Module.Dual κ V →ₗ[κ] C₁)),
      (∀ (a : R) (ξ : Module.Dual κ V),
        (c : R →ₗ[κ] (Module.Dual κ V →ₗ[κ] C₁)) a ξ ∈ LinearMap.ker d₁) →
      ∃ ĉ : ↥(Algebra.PointDerivations κ R ev (Module.Dual κ V →ₗ[κ] ↥(LinearMap.ker d₁))),
        ∀ (a : R) (ξ : Module.Dual κ V),
          (((ĉ : R →ₗ[κ] (Module.Dual κ V →ₗ[κ] ↥(LinearMap.ker d₁))) a ξ :
            ↥(LinearMap.ker d₁)) : C₁) =
            (c : R →ₗ[κ] (Module.Dual κ V →ₗ[κ] C₁)) a ξ) ∧
    (∀ (c : ↥(Algebra.PointDerivations κ R ev (Module.Dual κ V →ₗ[κ] C₁))) (ĉ : ↥(Algebra.PointDerivations κ R ev (Module.Dual κ V →ₗ[κ] ↥(LinearMap.ker d₁)))),
      (∀ (a : R) (ξ : Module.Dual κ V),
          (((ĉ : R →ₗ[κ] (Module.Dual κ V →ₗ[κ] ↥(LinearMap.ker d₁))) a ξ :
            ↥(LinearMap.ker d₁)) : C₁) =
            (c : R →ₗ[κ] (Module.Dual κ V →ₗ[κ] C₁)) a ξ) →
      Ψ c = Φ (Module.Dual κ V →ₗ[κ] H₁)
        (Algebra.PointDerivations.map (M := (Module.Dual κ V →ₗ[κ] ↥(LinearMap.ker d₁)))
          (M' := (Module.Dual κ V →ₗ[κ] H₁)) ev
          (LinearMap.llcomp κ (Module.Dual κ V) ↥(LinearMap.ker d₁) H₁ cls₁) ĉ)) ∧
    (∀ c c' : ↥(Algebra.PointDerivations κ R ev (Module.Dual κ V →ₗ[κ] C₁)),
      (∀ (a : R) (ξ : Module.Dual κ V),
        (c : R →ₗ[κ] (Module.Dual κ V →ₗ[κ] C₁)) a ξ ∈ LinearMap.ker d₁) →
      (∀ (a : R) (ξ : Module.Dual κ V),
        (c' : R →ₗ[κ] (Module.Dual κ V →ₗ[κ] C₁)) a ξ ∈ LinearMap.ker d₁) →
      (Ψ c = Ψ c' ↔
        ∀ (a : R) (ξ : Module.Dual κ V), ∃ b : C₀,
          d₀ b = (c : R →ₗ[κ] (Module.Dual κ V →ₗ[κ] C₁)) a ξ -
            (c' : R →ₗ[κ] (Module.Dual κ V →ₗ[κ] C₁)) a ξ)) ∧
    (∀ w : W ⊗[κ] (Module.Dual κ V →ₗ[κ] H₁),
      ∃ c : ↥(Algebra.PointDerivations κ R ev (Module.Dual κ V →ₗ[κ] C₁)),
        (∀ (a : R) (ξ : Module.Dual κ V),
          (c : R →ₗ[κ] (Module.Dual κ V →ₗ[κ] C₁)) a ξ ∈ LinearMap.ker d₁) ∧ Ψ c = w) ∧
    (∀ (c c' : ↥(Algebra.PointDerivations κ R ev (Module.Dual κ V →ₗ[κ] C₁))) (φ : V →ₗ[κ] V) (T : (Module.Dual κ V →ₗ[κ] H₁) →ₗ[κ] (Module.Dual κ V →ₗ[κ] H₁)),
      (∀ (F : Module.Dual κ V →ₗ[κ] H₁) (ξ : Module.Dual κ V),
        T F ξ = F (LinearMap.comp ξ φ)) →
      (∀ (a : R) (ξ : Module.Dual κ V),
        (c : R →ₗ[κ] (Module.Dual κ V →ₗ[κ] C₁)) a ξ ∈ LinearMap.ker d₁) →
      (∀ (a : R) (ξ : Module.Dual κ V),
        (c' : R →ₗ[κ] (Module.Dual κ V →ₗ[κ] C₁)) a ξ =
          (c : R →ₗ[κ] (Module.Dual κ V →ₗ[κ] C₁)) a (LinearMap.comp ξ φ)) →
      Ψ c' = TensorProduct.map (LinearMap.id : W →ₗ[κ] W) T (Ψ c)) := by
-- proof
  classical
  have : Module.Projective κ H₁ := Module.Projective.of_free
  let L : (Module.Dual κ V →ₗ[κ] ↥(LinearMap.ker d₁)) →ₗ[κ] (Module.Dual κ V →ₗ[κ] H₁) :=
    LinearMap.llcomp κ (Module.Dual κ V) ↥(LinearMap.ker d₁) H₁ cls₁
  have hL : ∀ (F : Module.Dual κ V →ₗ[κ] ↥(LinearMap.ker d₁)) (ξ : Module.Dual κ V),
      L F ξ = cls₁ (F ξ) :=
    fun F ξ => rfl
  let I : (Module.Dual κ V →ₗ[κ] ↥(LinearMap.ker d₁)) →ₗ[κ] (Module.Dual κ V →ₗ[κ] C₁) :=
    LinearMap.llcomp κ (Module.Dual κ V) ↥(LinearMap.ker d₁) C₁ (LinearMap.ker d₁).subtype
  have hI : ∀ (F : Module.Dual κ V →ₗ[κ] ↥(LinearMap.ker d₁)) (ξ : Module.Dual κ V),
      I F ξ = (F ξ : C₁) :=
    fun F ξ => rfl
  let HasLift : ↥(Algebra.PointDerivations κ R ev (Module.Dual κ V →ₗ[κ] C₁)) →
      ↥(Algebra.PointDerivations κ R ev (Module.Dual κ V →ₗ[κ] ↥(LinearMap.ker d₁))) → Prop :=
    fun c ĉ => ∀ (a : R) (ξ : Module.Dual κ V),
      (((ĉ : (R →ₗ[κ] (Module.Dual κ V →ₗ[κ] ↥(LinearMap.ker d₁)))) a ξ : ↥(LinearMap.ker d₁)) : C₁) =
        (c : (R →ₗ[κ] (Module.Dual κ V →ₗ[κ] C₁))) a ξ
  have huniq : ∀ (c : ↥(Algebra.PointDerivations κ R ev (Module.Dual κ V →ₗ[κ] C₁))) (ĉ ĉ' : ↥(Algebra.PointDerivations κ R ev (Module.Dual κ V →ₗ[κ] ↥(LinearMap.ker d₁)))),
      HasLift c ĉ → HasLift c ĉ' → ĉ = ĉ' := by
    intro c ĉ ĉ' h h'
    apply Subtype.ext
    refine LinearMap.ext fun a => LinearMap.ext fun ξ => Subtype.ext ?_
    rw [h a ξ, h' a ξ]
  have hlift : ∀ c : ↥(Algebra.PointDerivations κ R ev (Module.Dual κ V →ₗ[κ] C₁)),
      (∀ (a : R) (ξ : Module.Dual κ V),
        (c : (R →ₗ[κ] (Module.Dual κ V →ₗ[κ] C₁))) a ξ ∈ LinearMap.ker d₁) →
      ∃ ĉ : ↥(Algebra.PointDerivations κ R ev (Module.Dual κ V →ₗ[κ] ↥(LinearMap.ker d₁))),
        HasLift c ĉ := by
    intro c hc
    let D : (R →ₗ[κ] (Module.Dual κ V →ₗ[κ] ↥(LinearMap.ker d₁))) :=
      { toFun := fun a =>
          LinearMap.codRestrict (LinearMap.ker d₁) ((c : (R →ₗ[κ] (Module.Dual κ V →ₗ[κ] C₁))) a) (hc a)
        map_add' := by
          intro a b
          refine LinearMap.ext fun ξ => Subtype.ext ?_
          simp only [LinearMap.codRestrict_apply, map_add, LinearMap.add_apply, Submodule.coe_add]
        map_smul' := by
          intro r a
          refine LinearMap.ext fun ξ => Subtype.ext ?_
          simp only [LinearMap.codRestrict_apply, map_smul, LinearMap.smul_apply, Submodule.coe_smul,
            RingHom.id_apply] }
    have hD : ∀ (a : R) (ξ : Module.Dual κ V),
        ((D a ξ : ↥(LinearMap.ker d₁)) : C₁) =
          (c : (R →ₗ[κ] (Module.Dual κ V →ₗ[κ] C₁))) a ξ :=
      fun a ξ => rfl
    have hDmem : D ∈ Algebra.PointDerivations κ R ev (Module.Dual κ V →ₗ[κ] ↥(LinearMap.ker d₁)) := by
      intro a b
      refine LinearMap.ext fun ξ => Subtype.ext ?_
      rw [hD, c.2 a b]
      simp only [LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_add, Submodule.coe_smul, hD]
    refine ⟨⟨D, hDmem⟩, fun a ξ => hD a ξ⟩
  let Ψ : ↥(Algebra.PointDerivations κ R ev (Module.Dual κ V →ₗ[κ] C₁)) →
      W ⊗[κ] (Module.Dual κ V →ₗ[κ] H₁) :=
    fun c => if h : ∃ ĉ : ↥(Algebra.PointDerivations κ R ev (Module.Dual κ V →ₗ[κ] ↥(LinearMap.ker d₁))), HasLift c ĉ then
      Φ (Module.Dual κ V →ₗ[κ] H₁) (Algebra.PointDerivations.map ev L (Classical.choose h)) else 0
  have hpin : ∀ (c : ↥(Algebra.PointDerivations κ R ev (Module.Dual κ V →ₗ[κ] C₁))) (ĉ : ↥(Algebra.PointDerivations κ R ev (Module.Dual κ V →ₗ[κ] ↥(LinearMap.ker d₁)))),
      HasLift c ĉ →
      Ψ c = Φ (Module.Dual κ V →ₗ[κ] H₁) (Algebra.PointDerivations.map ev L ĉ) := by
    intro c ĉ hĉ
    have hex : ∃ ĉ : ↥(Algebra.PointDerivations κ R ev
        (Module.Dual κ V →ₗ[κ] ↥(LinearMap.ker d₁))), HasLift c ĉ := ⟨ĉ, hĉ⟩
    show (if h : ∃ ĉ : ↥(Algebra.PointDerivations κ R ev
        (Module.Dual κ V →ₗ[κ] ↥(LinearMap.ker d₁))), HasLift c ĉ then
      Φ (Module.Dual κ V →ₗ[κ] H₁) (Algebra.PointDerivations.map ev L (Classical.choose h)) else 0) = _
    rw [dite_eq_left hex, huniq c _ _ (Classical.choose_spec hex) hĉ]
  have hmapL : ∀ (ĉ : ↥(Algebra.PointDerivations κ R ev
        (Module.Dual κ V →ₗ[κ] ↥(LinearMap.ker d₁)))) (a : R) (ξ : Module.Dual κ V),
      (Algebra.PointDerivations.map ev L ĉ : R →ₗ[κ] (Module.Dual κ V →ₗ[κ] H₁)) a ξ =
        cls₁ ((ĉ : (R →ₗ[κ] (Module.Dual κ V →ₗ[κ] ↥(LinearMap.ker d₁)))) a ξ) :=
    fun _ _ _ => rfl
  refine ⟨Ψ, hlift, fun c ĉ hĉ => hpin c ĉ hĉ, ?_, ?_, ?_⟩
  ·
    intro c c' hc hc'
    obtain ⟨ĉ, hĉ⟩ := hlift c hc
    obtain ⟨ĉ', hĉ'⟩ := hlift c' hc'
    rw [hpin c ĉ hĉ, hpin c' ĉ' hĉ']
    constructor
    ·
      intro hΦ a ξ
      have h1 := (Φ (Module.Dual κ V →ₗ[κ] H₁)).injective hΦ
      have h2 : cls₁ ((ĉ : (R →ₗ[κ] (Module.Dual κ V →ₗ[κ] ↥(LinearMap.ker d₁)))) a ξ) =
          cls₁ ((ĉ' : (R →ₗ[κ] (Module.Dual κ V →ₗ[κ] ↥(LinearMap.ker d₁)))) a ξ) := by
        rw [← hmapL, ← hmapL, h1]
      have h3 : cls₁ ((ĉ : (R →ₗ[κ] (Module.Dual κ V →ₗ[κ] ↥(LinearMap.ker d₁)))) a ξ -
          (ĉ' : (R →ₗ[κ] (Module.Dual κ V →ₗ[κ] ↥(LinearMap.ker d₁)))) a ξ) = 0 := by
        rw [map_sub, h2, sub_self]
      rwa [hcls₁0, Submodule.coe_sub, hĉ, hĉ', LinearMap.mem_range] at h3
    ·
      intro h
      congr 1
      apply Subtype.ext
      refine LinearMap.ext fun a => LinearMap.ext fun ξ => ?_
      rw [hmapL, hmapL, ← sub_eq_zero, ← map_sub, hcls₁0, Submodule.coe_sub, hĉ, hĉ',
        LinearMap.mem_range]
      exact h a ξ
  ·
    intro w
    obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective cls₁ (LinearMap.range_eq_top.2 hcls₁)
    have hs' : ∀ y : H₁, cls₁ (s y) = y := fun y => by
      have := LinearMap.congr_fun hs y
      simpa using this
    let S : (Module.Dual κ V →ₗ[κ] H₁) →ₗ[κ] (Module.Dual κ V →ₗ[κ] ↥(LinearMap.ker d₁)) :=
      LinearMap.llcomp κ (Module.Dual κ V) H₁ ↥(LinearMap.ker d₁) s
    have hLS : LinearMap.comp L S = LinearMap.id := by
      refine LinearMap.ext fun F => LinearMap.ext fun ξ => ?_
      show cls₁ (s (F ξ)) = F ξ
      exact hs' (F ξ)
    let δ : ↥(Algebra.PointDerivations κ R ev (Module.Dual κ V →ₗ[κ] ↥(LinearMap.ker d₁))) :=
      (Φ (Module.Dual κ V →ₗ[κ] ↥(LinearMap.ker d₁))).symm
        (TensorProduct.map (LinearMap.id : W →ₗ[κ] W) S w)
    refine ⟨Algebra.PointDerivations.map ev I δ,
      fun a ξ => ((δ : (R →ₗ[κ] (Module.Dual κ V →ₗ[κ] ↥(LinearMap.ker d₁)))) a ξ).2, ?_⟩
    have hδ : HasLift (Algebra.PointDerivations.map ev I δ) δ := fun a ξ => rfl
    rw [hpin _ δ hδ, hΦnat, LinearEquiv.apply_symm_apply, ← LinearMap.comp_apply,
      ← TensorProduct.map_comp, LinearMap.id_comp, hLS, TensorProduct.map_id, LinearMap.id_apply]
  ·
    intro c c' φ T hT hc hc'
    obtain ⟨ĉ, hĉ⟩ := hlift c hc
    let P : (Module.Dual κ V →ₗ[κ] ↥(LinearMap.ker d₁)) →ₗ[κ]
      (Module.Dual κ V →ₗ[κ] ↥(LinearMap.ker d₁)) :=
      LinearMap.lcomp κ ↥(LinearMap.ker d₁) φ.dualMap
    have hP : ∀ (F : Module.Dual κ V →ₗ[κ] ↥(LinearMap.ker d₁)) (ξ : Module.Dual κ V),
        P F ξ = F (LinearMap.comp ξ φ) := by
      intro F ξ
      show F (φ.dualMap ξ) = F (LinearMap.comp ξ φ)
      rw [LinearMap.dualMap_apply']
    have hĉ' : HasLift c' (Algebra.PointDerivations.map ev P ĉ) := by
      intro a ξ
      show ((P ((ĉ : (R →ₗ[κ] (Module.Dual κ V →ₗ[κ] ↥(LinearMap.ker d₁)))) a) ξ :
          ↥(LinearMap.ker d₁)) : C₁) =
        (c' : (R →ₗ[κ] (Module.Dual κ V →ₗ[κ] C₁))) a ξ
      rw [hP, hĉ, hc']
    have hLP : LinearMap.comp L P = LinearMap.comp T L := by
      refine LinearMap.ext fun F => LinearMap.ext fun ξ => ?_
      show L (P F) ξ = T (L F) ξ
      rw [hT, hL, hP, hL]
    rw [hpin c ĉ hĉ, hpin c' _ hĉ', ← Algebra.PointDerivations.map_comp, hLP,
      Algebra.PointDerivations.map_comp, hΦnat]

-- created on 2026-10-13
