import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma mem_finset_inf {X : (Scheme : Type 1)} {ι : Type} (s : Finset ι) (f : ι → X.Opens) (x : X) :
  x ∈ s.inf f ↔ ∀ i ∈ s, x ∈ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.inf_insert, TopologicalSpace.Opens.mem_inf, ih]
    simp only [Finset.mem_insert, forall_eq_or_imp]
private lemma preimage_finset_inf {X Y : (Scheme : Type 1)} (φ : X ⟶ Y) {ι : Type} (s : Finset ι) (f : ι → Y.Opens) :
  ((TopologicalSpace.Opens.map φ.base).obj (s.inf f)) = s.inf fun i => ((TopologicalSpace.Opens.map φ.base).obj (f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.inf_insert, Finset.inf_insert, Scheme.Hom.preimage_inf, ih]
private lemma basicOpen_finset_prod {X : (Scheme : Type 1)} {U : X.Opens} {ι : Type} (s : Finset ι) (f : ι → (X.presheaf.obj (op U))) :
  X.basicOpen (∏ i ∈ s, f i) = U ⊓ s.inf fun i => X.basicOpen (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Scheme.basicOpen_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.inf_insert, Scheme.basicOpen_mul, ih, inf_left_comm]
private lemma hom_appLE_congr
  {X Y : (Scheme : Type 1)} {f₁ f₂ : X ⟶ Y} (h : f₁ = f₂) (U : Y.Opens) (V : X.Opens)
  (p₁ : V ≤ ((TopologicalSpace.Opens.map f₁.base).obj U)) (p₂ : V ≤ ((TopologicalSpace.Opens.map f₂.base).obj U)) (t : (Y.presheaf.obj (op U))) :
  f₁.appLE U V p₁ t = f₂.appLE U V p₂ t := by
  subst h
  rfl
private lemma map_appLE_apply
  {X Y : (Scheme : Type 1)} (f : X ⟶ Y) {U : Y.Opens} {V V' : X.Opens} (e : V ≤ ((TopologicalSpace.Opens.map f.base).obj U))
  (hV : V' ≤ V) (t : (Y.presheaf.obj (op U))) :
  X.presheaf.map (homOfLE hV).op (f.appLE U V e t) = f.appLE U V' (hV.trans e) t := by
  have h := CategoryTheory.ConcreteCategory.congr_hom (Scheme.Hom.appLE_map f e (homOfLE hV).op) t
  simpa only [CommRingCat.comp_apply] using h
private lemma appLE_map_apply
  {X Y : (Scheme : Type 1)} (f : X ⟶ Y) {U U' : Y.Opens} {V : X.Opens} (e : V ≤ ((TopologicalSpace.Opens.map f.base).obj U))
  (hU : U ≤ U') (t : (Y.presheaf.obj (op U'))) :
  f.appLE U V e (Y.presheaf.map (homOfLE hU).op t) = f.appLE U' V (e.trans (f.preimage_mono hU)) t := by
  have h := CategoryTheory.ConcreteCategory.congr_hom (Scheme.Hom.map_appLE f e (homOfLE hU).op) t
  simpa only [CommRingCat.comp_apply] using h
private lemma appLE_appLE_apply
  {X Y Z : (Scheme : Type 1)} (f : X ⟶ Y) (g : Y ⟶ Z) {U : Z.Opens} {V : Y.Opens} {W : X.Opens}
  (e₁ : V ≤ ((TopologicalSpace.Opens.map g.base).obj U)) (e₂ : W ≤ ((TopologicalSpace.Opens.map f.base).obj V)) (t : (Z.presheaf.obj (op U))) :
  f.appLE V W e₂ (g.appLE U V e₁ t) =
    (f ≫ g).appLE U W (e₂.trans ((Opens.map f.base).map (homOfLE e₁)).le) t := by
  have h := CategoryTheory.ConcreteCategory.congr_hom (Scheme.Hom.appLE_comp_appLE f g U V W e₁ e₂) t
  simpa only [CommRingCat.comp_apply] using h
/--
[AlgebraicGeometry_Scheme_exists_invariant_cocycle_basicOpen_eq_iInf_preimage_of_finite](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_exists_invariant_cocycle_basicOpen_eq_iInf_preimage_of_finite.lean)
-/
@[path]
private lemma main
  (X : (Scheme : Type 1)) (Γ : Type) [Group Γ] [Finite Γ] (ρ : Γ →* Aut X)
  (r : ℕ) (U : Fin r → X.Opens) (w : ∀ i : Fin r, Fin r → (X.presheaf.obj (op (U i)))) (hw1 : ∀ i, w i i = 1)
  (hw2 : ∀ i j k : Fin r, X.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (w i k) =
    X.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (w i j) *
      X.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (w j k))
  (hw3 : ∀ i j : Fin r, X.basicOpen (w i j) = U i ⊓ U j) :
  ∃ (U' : Fin r → X.Opens) (hinv : ∀ (γ : Γ) (i : Fin r), ((TopologicalSpace.Opens.map (ρ γ).hom.base).obj (U' i)) = U' i) (w' : ∀ i : Fin r, Fin r → (X.presheaf.obj (op (U' i)))), (∀ i, U' i = ⨅ γ : Γ, ((TopologicalSpace.Opens.map (ρ γ).hom.base).obj (U i))) ∧
    (∀ i, w' i i = 1) ∧
    (∀ i j k : Fin r, X.presheaf.map (homOfLE (inf_le_left : U' i ⊓ U' j ≤ U' i)).op (w' i k) =
      X.presheaf.map (homOfLE (inf_le_left : U' i ⊓ U' j ≤ U' i)).op (w' i j) *
        X.presheaf.map (homOfLE (inf_le_right : U' i ⊓ U' j ≤ U' j)).op (w' j k)) ∧
    (∀ i j : Fin r, X.basicOpen (w' i j) = U' i ⊓ U' j) ∧
    (∀ (γ : Γ) (i j : Fin r), (ρ γ).hom.appLE (U' i) (U' i) (le_of_eq (hinv γ i).symm) (w' i j) = w' i j) := by
  classical
  let _ : Fintype Γ := Fintype.ofFinite Γ
  let U' : Fin r → X.Opens := fun i => Finset.univ.inf fun γ : Γ => ((TopologicalSpace.Opens.map (ρ γ).hom.base).obj (U i))
  have hle : ∀ (γ : Γ) (i : Fin r), U' i ≤ ((TopologicalSpace.Opens.map (ρ γ).hom.base).obj (U i)) := fun γ i => Finset.inf_le (Finset.mem_univ γ)
  have hcomp : ∀ γ δ : Γ, (ρ δ).hom ≫ (ρ γ).hom = (ρ (γ * δ)).hom := fun γ δ => by
    rw [← Iso.trans_hom, ← Aut.Aut_mul_def, ← map_mul]
  have hinv : ∀ (γ : Γ) (i : Fin r), ((TopologicalSpace.Opens.map (ρ γ).hom.base).obj (U' i)) = U' i := by
    intro δ i
    change ((TopologicalSpace.Opens.map (ρ δ).hom.base).obj (Finset.univ.inf fun γ : Γ => ((TopologicalSpace.Opens.map (ρ γ).hom.base).obj (U i)))) = Finset.univ.inf fun γ : Γ => ((TopologicalSpace.Opens.map (ρ γ).hom.base).obj (U i))
    rw [preimage_finset_inf]
    apply le_antisymm
    ·
      apply Finset.le_inf
      intro γ _
      have e : ((TopologicalSpace.Opens.map (ρ δ).hom.base).obj ((TopologicalSpace.Opens.map (ρ (γ * δ⁻¹)).hom.base).obj (U i))) = ((TopologicalSpace.Opens.map (ρ γ).hom.base).obj (U i)) := by
        rw [← Scheme.Hom.comp_preimage, hcomp, inv_mul_cancel_right]
      rw [← e]
      apply Finset.inf_le (Finset.mem_univ (γ * δ⁻¹))
    ·
      apply Finset.le_inf
      intro γ _
      rw [← Scheme.Hom.comp_preimage, hcomp]
      apply Finset.inf_le (Finset.mem_univ (γ * δ))
  let w' : ∀ i : Fin r, Fin r → (X.presheaf.obj (op (U' i))) := fun i j => ∏ γ : Γ, (ρ γ).hom.appLE (U i) (U' i) (hle γ i) (w i j)
  refine ⟨U', hinv, w', fun i => (Finset.inf_univ_eq_iInf _), ?_, ?_, ?_, ?_⟩
  ·
    intro i
    simp only [w', hw1, map_one, Finset.prod_const_one]
  ·
    intro i j k
    rw [show w' i k = ∏ γ : Γ, (ρ γ).hom.appLE (U i) (U' i) (hle γ i) (w i k) from rfl,
      show w' i j = ∏ γ : Γ, (ρ γ).hom.appLE (U i) (U' i) (hle γ i) (w i j) from rfl,
      show w' j k = ∏ γ : Γ, (ρ γ).hom.appLE (U j) (U' j) (hle γ j) (w j k) from rfl,
      map_prod, map_prod, map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun γ _ => ?_
    rw [map_appLE_apply, map_appLE_apply, map_appLE_apply]
    have e : U' i ⊓ U' j ≤ ((TopologicalSpace.Opens.map (ρ γ).hom.base).obj (U i ⊓ U j)) := by
      rw [Scheme.Hom.preimage_inf]
      apply inf_le_inf (hle γ i) (hle γ j)
    have h := congrArg ((ρ γ).hom.appLE (U i ⊓ U j) (U' i ⊓ U' j) e) (hw2 i j k)
    rwa [map_mul, appLE_map_apply, appLE_map_apply, appLE_map_apply] at h
  ·
    intro i j
    rw [show w' i j = ∏ γ : Γ, (ρ γ).hom.appLE (U i) (U' i) (hle γ i) (w i j) from rfl, basicOpen_finset_prod]
    simp only [Scheme.basicOpen_appLE, hw3, Scheme.Hom.preimage_inf]
    apply le_antisymm
    ·
      refine inf_le_inf le_rfl ?_
      change (Finset.univ.inf fun γ : Γ => U' i ⊓ (((TopologicalSpace.Opens.map (ρ γ).hom.base).obj (U i)) ⊓ ((TopologicalSpace.Opens.map (ρ γ).hom.base).obj (U j)))) ≤
        Finset.univ.inf fun γ : Γ => ((TopologicalSpace.Opens.map (ρ γ).hom.base).obj (U j))
      apply Finset.inf_mono_fun fun γ _ => inf_le_right.trans inf_le_right
    ·
      refine le_inf inf_le_left (Finset.le_inf fun γ _ => ?_)
      apply le_inf inf_le_left (le_inf (inf_le_left.trans (hle γ i)) (inf_le_right.trans (hle γ j)))
  ·
    intro δ i j
    rw [show w' i j = ∏ γ : Γ, (ρ γ).hom.appLE (U i) (U' i) (hle γ i) (w i j) from rfl, map_prod]
    refine Fintype.prod_equiv (Equiv.mulRight δ) _ _ (fun γ => ?_)
    rw [appLE_appLE_apply, Equiv.coe_mulRight]
    apply hom_appLE_congr (hcomp γ δ) _ _ _ _ _


-- created on 2026-10-20
