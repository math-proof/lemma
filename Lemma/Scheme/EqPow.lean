import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

variable {Z : (Scheme : Type (u + 1))}
private lemma map_op_congr
  {A B : Z.Opens} (i j : B ⟶ A) (s : (Z.presheaf.obj (op A))) :
  Z.presheaf.map i.op s = Z.presheaf.map j.op s := by
  rw [Subsingleton.elim i j]
private lemma app_map_top
  {Z' : (Scheme : Type (u + 1))} (q : Z' ⟶ Z) (W : Z.Opens) (x : (Z.presheaf.obj (op ⊤))) :
  q.app W (Z.presheaf.map (homOfLE le_top).op x) = Z'.presheaf.map (homOfLE le_top).op (q.appTop x) := by
  have := congrArg (fun φ => φ.hom x) (q.naturality (homOfLE (le_top : W ≤ ⊤)).op)
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at this
  rw [this]
  apply map_op_congr _ _ _
private lemma comp_app_apply
  {X Y : (Scheme : Type (u + 1))} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Z.Opens) (x : (Z.presheaf.obj (op U))) :
  (f ≫ g).app U x = f.app ((TopologicalSpace.Opens.map g.base).obj U) (g.app U x) := rfl
private lemma root_pow
  [CommRing K] (k : ℕ) (g : K) :
  AdjoinRoot.root (Polynomial.X ^ k - Polynomial.C g) ^ k = algebraMap K (AdjoinRoot (Polynomial.X ^ k - Polynomial.C g)) g := by
  have h := AdjoinRoot.mk_self (f := (Polynomial.X ^ k - Polynomial.C g))
  rw [map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, sub_eq_zero] at h
  rw [h, AdjoinRoot.algebraMap_eq]
private lemma exists_pow_eq
  {X : (Scheme : Type (u + 1))} [IsIntegral X] (k : ℕ) (g : X.functionField)
  {X' : (Scheme : Type (u + 1))} (φ : X' ⟶ X) [QuasiCompact φ] [QuasiSeparated φ]
  (s : X ⟶ φ.normalization) (hs : s ≫ φ.fromNormalization = 𝟙 X)
  (V : X.Opens) (hV : IsAffineOpen V) (hηV : genericPoint X ∈ V)
  (θ : AdjoinRoot (Polynomial.X ^ k - Polynomial.C g : Polynomial X.functionField) →+* (X'.presheaf.obj (op ((TopologicalSpace.Opens.map φ.base).obj V))))
  (hθ : ∀ c : (X.presheaf.obj (op V)), φ.app V c = θ (algebraMap X.functionField _ (X.presheaf.germ V (genericPoint X) hηV c))) :
  ∃ f : X.functionField, f ^ k = g := by
  let _ : Nonempty V := ⟨⟨_, hηV⟩⟩
  let _ := functionField_isFractionRing_of_isAffineOpen X V hV
  let _ : Algebra (X.presheaf.obj (op V)) (X'.presheaf.obj (op ((TopologicalSpace.Opens.map φ.base).obj V))) := (φ.app V).hom.toAlgebra
  have halg : ∀ c : (X.presheaf.obj (op V)), algebraMap (X.presheaf.obj (op V)) (X'.presheaf.obj (op ((TopologicalSpace.Opens.map φ.base).obj V))) c = φ.app V c := fun c => rfl
  have hgerm : ∀ c : (X.presheaf.obj (op V)), X.presheaf.germ V (genericPoint X) hηV c = algebraMap (X.presheaf.obj (op V)) X.functionField c := fun c => rfl
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := (X.presheaf.obj (op V))) g
  have hb' : algebraMap (X.presheaf.obj (op V)) X.functionField b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  let e := φ.normalizationObjIso hV
  have hπ := φ.fromNormalization_app hV
  have hW : genericPoint X ∈ ((TopologicalSpace.Opens.map s.base).obj ((TopologicalSpace.Opens.map φ.fromNormalization.base).obj V)) := by
    rwa [← Scheme.Hom.comp_preimage, hs]
  let χ : integralClosure (X.presheaf.obj (op V)) (X'.presheaf.obj (op ((TopologicalSpace.Opens.map φ.base).obj V))) →+* X.functionField :=
    (X.presheaf.germ _ (genericPoint X) hW).hom.comp ((s.app (((TopologicalSpace.Opens.map φ.fromNormalization.base).obj V))).hom.comp e.inv.hom)
  have hχ : ∀ c : (X.presheaf.obj (op V)),
      χ (algebraMap (X.presheaf.obj (op V)) (integralClosure (X.presheaf.obj (op V)) (X'.presheaf.obj (op ((TopologicalSpace.Opens.map φ.base).obj V)))) c) =
        algebraMap (X.presheaf.obj (op V)) X.functionField c := by
    intro c
    have h1 : e.inv (algebraMap (X.presheaf.obj (op V)) (integralClosure (X.presheaf.obj (op V)) (X'.presheaf.obj (op ((TopologicalSpace.Opens.map φ.base).obj V)))) c) =
        φ.fromNormalization.app V c := by
      rw [hπ]
      rfl
    have hpre : ((TopologicalSpace.Opens.map s.base).obj ((TopologicalSpace.Opens.map φ.fromNormalization.base).obj V)) = V := by
      rw [← Scheme.Hom.comp_preimage, hs]
      apply Scheme.Hom.id_preimage
    have h2 : s.app ((TopologicalSpace.Opens.map φ.fromNormalization.base).obj V) (φ.fromNormalization.app V c) =
        X.presheaf.map (eqToHom hpre).op c := by
      rw [← comp_app_apply, Scheme.Hom.congr_app hs V, CommRingCat.comp_apply, Scheme.Hom.id_app]
      apply map_op_congr _ _ _
    simp only [χ, RingHom.coe_comp, Function.comp_apply]
    rw [h1, h2, TopCat.Presheaf.germ_res_apply]
    rfl
  obtain hk | hk := Nat.eq_zero_or_pos k
  ·
    subst hk
    refine ⟨1, ?_⟩
    have hL : (1 : AdjoinRoot (Polynomial.X ^ 0 - Polynomial.C g : Polynomial X.functionField)) =
        algebraMap _ _ g := (pow_zero _).symm.trans (root_pow 0 g)
    have hga : X.presheaf.germ V (genericPoint X) hηV a =
        g * X.presheaf.germ V (genericPoint X) hηV b := by
      rw [hgerm, hgerm, ← hab, div_mul_cancel₀ _ hb']
    have hφab : φ.app V a = φ.app V b := by
      rw [hθ, hθ, hga, map_mul, map_mul, ← hL, map_one, one_mul]
    have hIC : algebraMap (X.presheaf.obj (op V)) (integralClosure (X.presheaf.obj (op V)) (X'.presheaf.obj (op ((TopologicalSpace.Opens.map φ.base).obj V)))) a =
        algebraMap (X.presheaf.obj (op V)) (integralClosure (X.presheaf.obj (op V)) (X'.presheaf.obj (op ((TopologicalSpace.Opens.map φ.base).obj V)))) b := by
      apply Subtype.ext
      change algebraMap (X.presheaf.obj (op V)) (X'.presheaf.obj (op ((TopologicalSpace.Opens.map φ.base).obj V))) a = algebraMap (X.presheaf.obj (op V)) (X'.presheaf.obj (op ((TopologicalSpace.Opens.map φ.base).obj V))) b
      rw [halg, halg, hφab]
    have := congrArg χ hIC
    rw [hχ, hχ] at this
    rw [pow_zero, ← hab, this, div_self hb']
  ·
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    have hK : algebraMap (X.presheaf.obj (op V)) X.functionField b ^ (m + 1) * g =
        algebraMap (X.presheaf.obj (op V)) X.functionField (b ^ m * a) := by
      rw [← hab, map_mul, map_pow]
      field_simp
      ring
    let tb : AdjoinRoot (Polynomial.X ^ (m + 1) - Polynomial.C g : Polynomial X.functionField) :=
      algebraMap X.functionField _ (algebraMap (X.presheaf.obj (op V)) X.functionField b) *
        AdjoinRoot.root (Polynomial.X ^ (m + 1) - Polynomial.C g)
    have htb : tb ^ (m + 1) =
        algebraMap X.functionField _ (algebraMap (X.presheaf.obj (op V)) X.functionField (b ^ m * a)) := by
      simp only [tb]
      rw [mul_pow, ← map_pow, root_pow, ← map_mul, hK]
    have he₀ : θ tb ^ (m + 1) = φ.app V (b ^ m * a) := by
      rw [← map_pow, htb, ← hgerm, ← hθ]
    have hint : IsIntegral (X.presheaf.obj (op V)) (θ tb) := by
      refine ⟨Polynomial.X ^ (m + 1) - Polynomial.C (b ^ m * a), Polynomial.monic_X_pow_sub_C _ (by omega), ?_⟩
      simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, he₀, halg, sub_self]
    let y : integralClosure (X.presheaf.obj (op V)) (X'.presheaf.obj (op ((TopologicalSpace.Opens.map φ.base).obj V))) := ⟨θ tb, hint⟩
    have hy : y ^ (m + 1) = algebraMap (X.presheaf.obj (op V)) (integralClosure (X.presheaf.obj (op V)) (X'.presheaf.obj (op ((TopologicalSpace.Opens.map φ.base).obj V)))) (b ^ m * a) := by
      apply Subtype.ext
      change θ tb ^ (m + 1) = algebraMap (X.presheaf.obj (op V)) (X'.presheaf.obj (op ((TopologicalSpace.Opens.map φ.base).obj V))) (b ^ m * a)
      rw [he₀, halg]
    have hF : χ y ^ (m + 1) = algebraMap (X.presheaf.obj (op V)) X.functionField (b ^ m * a) := by
      rw [← map_pow, hy, hχ]
    refine ⟨χ y / algebraMap (X.presheaf.obj (op V)) X.functionField b, ?_⟩
    rw [div_pow, hF, ← hab, map_mul, map_pow]
    field_simp
    ring
/--
[AlgebraicGeometry_exists_pow_eq_of_section_fromNormalization_kummer](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_exists_pow_eq_of_section_fromNormalization_kummer.lean)
-/
@[path]
private lemma main
  {X : (Scheme : Type (u + 1))} [IsIntegral X] (k : ℕ) (g : X.functionField) (_ : g ≠ 0)
  (s : X ⟶ (Spec.map (CommRingCat.ofHom (algebraMap X.functionField (AdjoinRoot (Polynomial.X ^ k - Polynomial.C g : Polynomial X.functionField)))) ≫ X.fromSpecStalk (genericPoint X)).normalization)
  (hs : s ≫ (Spec.map (CommRingCat.ofHom (algebraMap X.functionField (AdjoinRoot (Polynomial.X ^ k - Polynomial.C g : Polynomial X.functionField)))) ≫ X.fromSpecStalk (genericPoint X)).fromNormalization = 𝟙 X) :
  ∃ f : X.functionField, f ^ k = g := by
  let V : X.Opens := (X.affineCover.f (X.affineCover.idx (genericPoint X))).opensRange
  have hV : IsAffineOpen V := isAffineOpen_opensRange _
  have hηV : genericPoint X ∈ V := X.affineCover.covers _
  refine exists_pow_eq k g _ s hs V hV hηV
    (((Spec (CommRingCat.of (AdjoinRoot (Polynomial.X ^ k - Polynomial.C g : Polynomial X.functionField)))).presheaf.map
        (homOfLE le_top).op).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of
        (AdjoinRoot (Polynomial.X ^ k - Polynomial.C g : Polynomial X.functionField)))).inv.hom) ?_
  intro c
  rw [comp_app_apply, Scheme.fromSpecStalk_app hηV, CommRingCat.comp_apply, CommRingCat.comp_apply]
  erw [app_map_top]
  have hnat := congrArg (fun ψ => ψ.hom (X.presheaf.germ V (genericPoint X) hηV c))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap X.functionField
      (AdjoinRoot (Polynomial.X ^ k - Polynomial.C g : Polynomial X.functionField)))))
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at hnat
  simp only [RingHom.coe_comp, Function.comp_apply]
  erw [← hnat]
  apply map_op_congr _ _ _


-- created on 2026-10-20
