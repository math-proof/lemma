import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open TensorProduct


private lemma injective_map_equalizer_val_and_range_eq
  (R A T : Type*) [CommRing R] [CommRing A] [Algebra R A] [CommRing T] [Algebra R T] [Module.Flat R T]
  {ι : Type*} [Finite ι] (σ : ι → (A →ₐ[R] A)) :
  let act : A →ₐ[R] (ι → A) := AlgHom.pi (fun i => σ i)
  let diag : A →ₐ[R] (ι → A) := AlgHom.pi (fun _ => AlgHom.id R A)
  Function.Injective (Algebra.TensorProduct.map (AlgHom.id T T) (AlgHom.equalizer act diag).val) ∧
  Set.range (Algebra.TensorProduct.map (AlgHom.id T T) (AlgHom.equalizer act diag).val) =
    {x : T ⊗[R] A | ∀ i : ι, Algebra.TensorProduct.map (AlgHom.id T T) (σ i) x = x} := by
  classical
  intro act diag
  have : Fintype ι := Fintype.ofFinite ι
  let e := AlgHom.tensorEqualizerEquiv T T act diag
  have hfac : ∀ x, Algebra.TensorProduct.map (AlgHom.id T T) (AlgHom.equalizer act diag).val x = (e x : T ⊗[R] A) := by
    intro x
    rw [AlgHom.tensorEqualizerEquiv_apply, AlgHom.coe_tensorEqualizer]
  let p := Algebra.TensorProduct.piRight R T T (fun _ : ι => A)
  have h1 : ∀ (x : T ⊗[R] A) (i : ι), p (Algebra.TensorProduct.map (AlgHom.id T T) act x) i =
      Algebra.TensorProduct.map (AlgHom.id T T) (σ i) x := by
    intro x i
    induction x using TensorProduct.inductionOn with
    | tmul t a => simp [p, act, Algebra.TensorProduct.piRight_tmul]
    | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
  have h2 : ∀ (x : T ⊗[R] A) (i : ι), p (Algebra.TensorProduct.map (AlgHom.id T T) diag x) i = x := by
    intro x i
    induction x using TensorProduct.inductionOn with
    | tmul t a => simp [p, diag, Algebra.TensorProduct.piRight_tmul]
    | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
  have key : ∀ x : T ⊗[R] A,
      x ∈ AlgHom.equalizer (Algebra.TensorProduct.map (AlgHom.id T T) act)
        (Algebra.TensorProduct.map (AlgHom.id T T) diag) ↔
      ∀ i : ι, Algebra.TensorProduct.map (AlgHom.id T T) (σ i) x = x := by
    intro x
    if hι : Nonempty ι then
      rw [AlgHom.mem_equalizer, ← p.injective.eq_iff, funext_iff]
      apply forall_congr' fun i => by rw [h1, h2]
    else
      rw [AlgHom.mem_equalizer]
      have : IsEmpty ι := not_nonempty_iff.mp hι
      constructor
      ·
        intro _ i; exact (IsEmpty.false i).elim
      ·
        intro _; apply p.injective; funext i; exact (IsEmpty.false i).elim
  refine ⟨?_, ?_⟩
  ·
    intro x y hxy
    rw [hfac, hfac] at hxy
    apply e.injective (Subtype.ext hxy)
  ·
    ext z
    simp only [Set.mem_range, Set.mem_ofPred_eq]
    constructor
    ·
      rintro ⟨x, rfl⟩
      rw [hfac]
      apply (key _).1 (e x).2
    ·
      intro hz
      refine ⟨e.symm ⟨z, (key z).2 hz⟩, ?_⟩
      rw [hfac, AlgEquiv.apply_symm_apply]

private lemma algebraMap_tensor_injective_and_range_eq
  (R A T : Type*) [CommRing R] [CommRing A] [Algebra R A] [CommRing T] [Algebra R T] [Module.Flat R T]
  {ι : Type*} [Finite ι] (σ : ι → (A →ₐ[R] A))
  (hinj : Function.Injective (algebraMap R A))
  (hrange : Set.range (algebraMap R A) = {a | ∀ i, σ i a = a}) :
  Function.Injective (algebraMap T (T ⊗[R] A)) ∧
  Set.range (algebraMap T (T ⊗[R] A)) =
    {x : T ⊗[R] A | ∀ i : ι, Algebra.TensorProduct.map (AlgHom.id T T) (σ i) x = x} := by
  classical
  obtain ⟨hinjE, hrangeE⟩ := injective_map_equalizer_val_and_range_eq R A T σ
  set act : A →ₐ[R] (ι → A) := AlgHom.pi (fun i => σ i) with hact
  set diag : A →ₐ[R] (ι → A) := AlgHom.pi (fun _ => AlgHom.id R A) with hdiag
  set E := AlgHom.equalizer act diag with hE
  have hmemE : ∀ a : A, a ∈ E ↔ ∀ i, σ i a = a := by
    intro a
    simp only [hE, AlgHom.mem_equalizer, hact, hdiag, AlgHom.pi_apply, AlgHom.id_apply, funext_iff]
  have hRE : ∀ r : R, algebraMap R A r ∈ E := fun r => (hmemE _).2 fun i => (σ i).commutes r
  let ψ : R →ₐ[R] E := (Algebra.ofId R A).codRestrict E hRE
  have hψ : Function.Bijective ψ := by
    refine ⟨fun a b h => hinj (congrArg (fun x : E => (x : A)) h), fun y => ?_⟩
    have : (y : A) ∈ Set.range (algebraMap R A) := by rw [hrange]; apply (hmemE _).1 y.2
    obtain ⟨r, hr⟩ := this
    exact ⟨r, Subtype.ext hr⟩
  let ψe : R ≃ₐ[R] E := AlgEquiv.ofBijective ψ hψ
  have hfac : ∀ t : T, algebraMap T (T ⊗[R] A) t =
      Algebra.TensorProduct.map (AlgHom.id T T) E.val
        (Algebra.TensorProduct.map (AlgHom.id T T) (ψe : R →ₐ[R] E) ((Algebra.TensorProduct.rid R T T).symm t)) := by
    intro t
    simp [Algebra.TensorProduct.algebraMap_apply, ψe, ψ]
  have hc1 : (Algebra.TensorProduct.map (AlgHom.id T T) (ψe.symm : E →ₐ[R] R)).comp
    (Algebra.TensorProduct.map (AlgHom.id T T) (ψe : R →ₐ[R] E)) = AlgHom.id T (T ⊗[R] R) := by
    rw [← Algebra.TensorProduct.map_comp]
    have : ((ψe.symm : E →ₐ[R] R).comp (ψe : R →ₐ[R] E)) = AlgHom.id R R := by ext
    rw [this, AlgHom.comp_id, Algebra.TensorProduct.map_id]
  have hc2 : (Algebra.TensorProduct.map (AlgHom.id T T) (ψe : R →ₐ[R] E)).comp
    (Algebra.TensorProduct.map (AlgHom.id T T) (ψe.symm : E →ₐ[R] R)) = AlgHom.id T (T ⊗[R] E) := by
    rw [← Algebra.TensorProduct.map_comp]
    have : ((ψe : R →ₐ[R] E).comp (ψe.symm : E →ₐ[R] R)) = AlgHom.id R E := by ext; simp
    rw [this, AlgHom.comp_id, Algebra.TensorProduct.map_id]
  have hsurjmid : Function.Surjective (fun t : T =>
      Algebra.TensorProduct.map (AlgHom.id T T) (ψe : R →ₐ[R] E) ((Algebra.TensorProduct.rid R T T).symm t)) := by
    intro y
    refine ⟨Algebra.TensorProduct.rid R T T (Algebra.TensorProduct.map (AlgHom.id T T) (ψe.symm : E →ₐ[R] R) y), ?_⟩
    simp only [AlgEquiv.symm_apply_apply]
    rw [← AlgHom.comp_apply, hc2, AlgHom.id_apply]
  have hinjmid : Function.Injective (fun t : T =>
      Algebra.TensorProduct.map (AlgHom.id T T) (ψe : R →ₐ[R] E) ((Algebra.TensorProduct.rid R T T).symm t)) := by
    intro a b h
    have h' := congrArg (fun y => Algebra.TensorProduct.rid R T T (Algebra.TensorProduct.map (AlgHom.id T T) (ψe.symm : E →ₐ[R] R) y)) h
    simp only at h'
    rw [← AlgHom.comp_apply, ← AlgHom.comp_apply (Algebra.TensorProduct.map _ _), hc1, AlgHom.id_apply, AlgHom.id_apply,
      AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply] at h'
    exact h'
  refine ⟨?_, ?_⟩
  ·
    intro a b h
    rw [hfac, hfac] at h
    apply hinjmid (hinjE h)
  ·
    ext z
    constructor
    ·
      rintro ⟨t, rfl⟩
      rw [hfac]
      apply (hrangeE.le ⟨_, rfl⟩ : _)
    ·
      intro hz
      obtain ⟨y, hy⟩ := (hrangeE.ge hz : z ∈ Set.range _)
      obtain ⟨t, rfl⟩ := hsurjmid y
      exact ⟨t, by rw [hfac]; apply hy⟩

private lemma appLE_congr_hom {X Y : Scheme.{0}} {f g : X ⟶ Y} (h : f = g) (U : Y.Opens) (V : X.Opens)
  (e : V ≤ f ⁻¹ᵁ U) : f.appLE U V e = g.appLE U V (h ▸ e) := by
  subst h; rfl
/--
[AlgebraicGeometry_Scheme_app_basicOpen_injective_and_range_eq_invariants_of_flat](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_app_basicOpen_injective_and_range_eq_invariants_of_flat.lean)
-/
@[path]
private lemma main
  [CommRing B₀] [CommRing 𝒪] [Group H] [Finite H]
  {i : B₀ →+* 𝒪}
  {M X : Scheme.{0}}
  {πM : M ⟶ Spec (CommRingCat.of B₀)}
  {πX : X ⟶ Spec (CommRingCat.of B₀)}
  {π : M ⟶ X}
  {ρ : H →* Aut M}
  {M' X' : Scheme.{0}}
  {πM' : M' ⟶ Spec (CommRingCat.of 𝒪)}
  {πX' : X' ⟶ Spec (CommRingCat.of 𝒪)}
  {gM : M' ⟶ M}
  {gX : X' ⟶ X}
  {π' : M' ⟶ X'}
  {ρ' : H →* Aut M'}
  {V : X.Opens}
  {r : Γ(X', gX ⁻¹ᵁ V)}
-- given
  (hi : Flat (Spec.map (CommRingCat.ofHom i)))
  (hπX : π ≫ πX = πM)
  (_hover : ∀ h : H, (ρ h).hom ≫ πM = πM)
  (hπ : ∀ h : H, (ρ h).hom ≫ π = π)
  (_hint : IsIntegralHom π)
  (haff : IsAffineHom π)
  (_hsurj : Function.Surjective π.base)
  (hsec : ∀ V : X.Opens, Function.Injective (π.app V))
  (hinv : ∀ V : X.Opens, Set.range (π.app V) = {s | ∀ h : H, (ρ h).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) (by rw [← Scheme.Hom.comp_preimage, hπ h]) s = s})
  (hgM : IsPullback gM πM' πM (Spec.map (CommRingCat.ofHom i)))
  (hgX : IsPullback gX πX' πX (Spec.map (CommRingCat.ofHom i)))
  (hπX' : π' ≫ πX' = πM')
  (hπg : π' ≫ gX = gM ≫ π)
  (_hover' : ∀ h : H, (ρ' h).hom ≫ πM' = πM')
  (hρg : ∀ h : H, (ρ' h).hom ≫ gM = gM ≫ (ρ h).hom)
  (hπ' : ∀ h : H, (ρ' h).hom ≫ π' = π')
  (hV : IsAffineOpen V) :
-- imply
  Function.Injective (π'.app (X'.basicOpen r)) ∧
    Set.range (π'.app (X'.basicOpen r)) =
      {s | ∀ h : H, (ρ' h).hom.appLE (π' ⁻¹ᵁ X'.basicOpen r) (π' ⁻¹ᵁ X'.basicOpen r)
        (by rw [← Scheme.Hom.comp_preimage, hπ' h]) s = s} := by
-- proof
  classical
    have hsq : IsPullback gM π' π gX := by
      refine IsPullback.of_bot (h₃₁ := Spec.map (CommRingCat.ofHom i)) (v₂₁ := πX') (v₂₂ := πX) ?_ hπg.symm hgX
      rw [hπX', hπX]; apply hgM
    have : IsAffineHom gX := MorphismProperty.of_isPullback hgX.flip inferInstance
    have : Flat gX := MorphismProperty.of_isPullback hgX.flip hi
    set D : X'.Opens := X'.basicOpen r with hDdef
    have hDW : D ≤ gX ⁻¹ᵁ V := X'.basicOpen_le r
    have hU : IsAffineOpen (π ⁻¹ᵁ V) := hV.preimage π
    have hW : IsAffineOpen (gX ⁻¹ᵁ V) := hV.preimage gX
    have hD : IsAffineOpen D := hW.basicOpen r
    have hUst : ∀ h : H, (ρ h).hom ⁻¹ᵁ (π ⁻¹ᵁ V) = π ⁻¹ᵁ V := fun h => by rw [← Scheme.Hom.comp_preimage, hπ h]
    have hD'le : π' ⁻¹ᵁ D ≤ gM ⁻¹ᵁ (π ⁻¹ᵁ V) := by
      rw [← Scheme.Hom.comp_preimage, ← hπg, Scheme.Hom.comp_preimage]
      apply Scheme.Hom.preimage_mono π' hDW
    have hD'eq : π' ⁻¹ᵁ D = gM ⁻¹ᵁ (π ⁻¹ᵁ V) ⊓ π' ⁻¹ᵁ D := (inf_eq_right.mpr hD'le).symm
    have HP : IsPushout (π.appLE V (π ⁻¹ᵁ V) le_rfl) (gX.appLE V D hDW)
      (gM.appLE (π ⁻¹ᵁ V) (π' ⁻¹ᵁ D) (by simp [hD'le])) (π'.appLE D (π' ⁻¹ᵁ D) (by simp)) :=
      (isIso_pushoutSection_iff hsq hDW le_rfl hD'eq).mp (isIso_pushoutSection_of_isAffineOpen hsq hDW le_rfl hD'eq hV hD hU)
    let R : Type := Γ(X, V)
    let A : Type := Γ(M, π ⁻¹ᵁ V)
    let T : Type := Γ(X', D)
    let algRA : Algebra R A := (π.appLE V (π ⁻¹ᵁ V) le_rfl).hom.toAlgebra
    let algRT : Algebra R T := (gX.appLE V D hDW).hom.toAlgebra
    have hσcomm : ∀ (h : H) (x : R), (ρ h).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) (by rw [hUst h]) (π.appLE V (π ⁻¹ᵁ V) le_rfl x) =
        π.appLE V (π ⁻¹ᵁ V) le_rfl x := by
      intro h x
      rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE, appLE_congr_hom (hπ h)]
    let σ : H → (A →ₐ[R] A) := fun h =>
      { ((ρ h).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) (by rw [hUst h])).hom with commutes' := fun x => hσcomm h x }
    have hσ : ∀ (h : H) (a : A), σ h a = (ρ h).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) (by rw [hUst h]) a := fun _ _ => rfl
    have hinjR : Function.Injective (algebraMap R A) := by
      show Function.Injective (π.appLE V (π ⁻¹ᵁ V) le_rfl)
      rw [Scheme.Hom.appLE_eq_app]; apply hsec V
    have hrangeR : Set.range (algebraMap R A) = {a | ∀ h : H, σ h a = a} := by
      show Set.range (π.appLE V (π ⁻¹ᵁ V) le_rfl) = _
      rw [Scheme.Hom.appLE_eq_app, hinv V]
      rfl
    have : IsAffine D := hD
    have : IsAffine V := hV
    have : Module.Flat R T := by
      rw [← RingHom.flat_algebraMap_iff]
      show (gX.appLE V D hDW).hom.Flat
      have h1 := Scheme.Hom.flat_appTop (gX.resLE V D hDW)
      rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top] at h1
      have h2 : (V.topIso.inv ≫ (V.topIso.hom ≫ gX.appLE V D hDW ≫ D.topIso.inv) ≫ D.topIso.hom).hom.Flat :=
        ((RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso V.topIso.inv)).comp h1).comp
          (RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso D.topIso.hom))
      simpa only [Category.assoc, Iso.inv_hom_id, Iso.inv_hom_id_assoc, Category.comp_id] using h2
    obtain ⟨hinjT, hrangeT⟩ := algebraMap_tensor_injective_and_range_eq R A T σ hinjR hrangeR
    have HT : IsPushout (gX.appLE V D hDW) (π.appLE V (π ⁻¹ᵁ V) le_rfl)
      (CommRingCat.ofHom (S := T ⊗[R] A) Algebra.TensorProduct.includeLeftRingHom)
      (CommRingCat.ofHom (S := T ⊗[R] A) (Algebra.TensorProduct.includeRight (R := R) (A := T) (B := A)).toRingHom) :=
      CommRingCat.isPushout_tensorProduct R T A
    let Θ := HT.isoIsPushout _ _ HP.flip
    have hΘl : CommRingCat.ofHom (S := T ⊗[R] A) Algebra.TensorProduct.includeLeftRingHom ≫ Θ.hom =
        π'.appLE D (π' ⁻¹ᵁ D) (by simp) := HT.inl_isoIsPushout_hom _ _ HP.flip
    have hΘr : CommRingCat.ofHom (S := T ⊗[R] A) (Algebra.TensorProduct.includeRight (R := R) (A := T) (B := A)).toRingHom ≫ Θ.hom =
        gM.appLE (π ⁻¹ᵁ V) (π' ⁻¹ᵁ D) (by simp [hD'le]) := HT.inr_isoIsPushout_hom _ _ HP.flip
    have hΘl' : ∀ t : T, Θ.hom (t ⊗ₜ[R] (1 : A)) = π'.app D t := by
      intro t
      have := congrArg (fun φ => φ.hom t) hΘl
      simpa [Scheme.Hom.appLE_eq_app] using this
    have hΘr' : ∀ a : A, Θ.hom ((1 : T) ⊗ₜ[R] a) = gM.appLE (π ⁻¹ᵁ V) (π' ⁻¹ᵁ D) (by simp [hD'le]) a := by
      intro a
      have := congrArg (fun φ => φ.hom a) hΘr
      simpa using this
    have hinter : ∀ (h : H) (x : T ⊗[R] A),
        Θ.hom (Algebra.TensorProduct.map (AlgHom.id T T) (σ h) x) =
          (ρ' h).hom.appLE (π' ⁻¹ᵁ D) (π' ⁻¹ᵁ D) (by rw [← Scheme.Hom.comp_preimage, hπ' h]) (Θ.hom x) := by
      intro h x
      induction x using TensorProduct.inductionOn with
      | tmul t a =>
        have e1 : t ⊗ₜ[R] a = (t ⊗ₜ[R] (1 : A)) * ((1 : T) ⊗ₜ[R] a) := by
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        have e2 : t ⊗ₜ[R] (σ h a) = (t ⊗ₜ[R] (1 : A)) * ((1 : T) ⊗ₜ[R] (σ h a)) := by
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, e2, e1, map_mul, map_mul, map_mul, hΘl', hΘr', hΘr']
        congr 1
        ·
          rw [Scheme.Hom.app_eq_appLE, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE,
            appLE_congr_hom (hπ' h)]
        ·
          rw [hσ, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE,
            Scheme.Hom.appLE_comp_appLE, appLE_congr_hom (hρg h)]
      | add x y hx hy => simp only [map_add, hx, hy]
    have hΘbij : Function.Bijective Θ.hom := ConcreteCategory.bijective_of_isIso Θ.hom
    have happ : ∀ t : T, π'.app D t = Θ.hom (algebraMap T (T ⊗[R] A) t) := fun t => by
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, hΘl']
    refine ⟨?_, ?_⟩
    ·
      intro t₁ t₂ h12
      rw [happ, happ] at h12
      apply hinjT (hΘbij.1 h12)
    ·
      ext s
      constructor
      ·
        rintro ⟨t, rfl⟩ h
        have hfix : Algebra.TensorProduct.map (AlgHom.id T T) (σ h) (algebraMap T (T ⊗[R] A) t) = algebraMap T (T ⊗[R] A) t :=
          (hrangeT.le ⟨t, rfl⟩) h
        rw [happ, ← hinter, hfix]
      ·
        intro hs
        obtain ⟨x, rfl⟩ := hΘbij.2 s
        have hx : ∀ h : H, Algebra.TensorProduct.map (AlgHom.id T T) (σ h) x = x :=
          fun h => hΘbij.1 (by rw [hinter]; apply hs h)
        obtain ⟨t, ht⟩ := (hrangeT.ge hx : x ∈ Set.range (algebraMap T (T ⊗[R] A)))
        exact ⟨t, by rw [happ, ht]⟩


-- created on 2026-10-23
