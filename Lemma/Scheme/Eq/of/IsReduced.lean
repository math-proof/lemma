import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma eq_zero_of_forall_algHom
  {k : Type u} [Field k] [IsAlgClosed k]
  {A : Type u} [CommRing A] [Algebra k A] [IsReduced A] [Algebra.FiniteType k A]
    (U : Set (PrimeSpectrum A)) (hUo : IsOpen U) (hU : Dense U) (a : A)
    (ha : ∀ m : PrimeSpectrum A, m ∈ U → ∀ y : AlgHom k A k, RingHom.ker (y : RingHom A k) = m.asIdeal → y a = 0) : a = 0 := by
  classical
  by_contra h0
  have hna : ¬ IsNilpotent a := fun h => h0 h.eq_zero
  have hD : ((PrimeSpectrum.basicOpen a : TopologicalSpace.Opens (PrimeSpectrum A)) :
      Set (PrimeSpectrum A)).Nonempty := by
    by_contra hne
    apply hna
    rw [← PrimeSpectrum.basicOpen_eq_bot_iff]
    ext x
    simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
    exact fun hx => hne ⟨x, hx⟩
  obtain ⟨x, hxa, hxU⟩ := hU.inter_open_nonempty _ (PrimeSpectrum.basicOpen a).isOpen hD
  let _ : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := k) (B := A)
  obtain ⟨m, ⟨hma, hmU⟩, hmc⟩ := (jacobsonSpace_iff_locallyClosed.mp inferInstance)
    (((PrimeSpectrum.basicOpen a : TopologicalSpace.Opens (PrimeSpectrum A)) : Set (PrimeSpectrum A)) ∩ U)
    ⟨x, hxa, hxU⟩ (((PrimeSpectrum.basicOpen a).isOpen.inter hUo).isLocallyClosed)
  rw [mem_closedPoints_iff, PrimeSpectrum.isClosed_singleton_iff_isMaximal] at hmc
  let _ := Ideal.Quotient.field m.asIdeal
  let _ : Module.Finite k (A ⧸ m.asIdeal) := finite_of_finite_type_of_isJacobsonRing k _
  have hbij := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := A ⧸ m.asIdeal)
  let e : k ≃ₐ[k] (A ⧸ m.asIdeal) := AlgEquiv.ofBijective (Algebra.ofId k _) hbij
  let y : AlgHom k A k := (e.symm : AlgHom k (A ⧸ m.asIdeal) k).comp (Ideal.Quotient.mkₐ k m.asIdeal)
  have hy : RingHom.ker (y : RingHom A k) = m.asIdeal := by
    ext b
    simp only [RingHom.mem_ker, AlgHom.coe_toRingHom, AlgHom.coe_comp, Function.comp_apply, Ideal.Quotient.mkₐ_eq_mk, y, AlgEquiv.coe_toAlgHom, map_eq_zero_iff _ e.symm.injective, Ideal.Quotient.eq_zero_iff_mem]
  have h1 := ha m hmU y hy
  apply (PrimeSpectrum.mem_basicOpen _ _).mp hma
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have : e.symm (Ideal.Quotient.mk m.asIdeal a) = 0 := by simpa [y] using h1
  simpa using this
private lemma exists_eq_tmul_one_add_tmul_eps
  {k : Type u} [Field k] {A : Type u} [CommRing A] [Algebra k A]
  (r : TensorProduct k A (DualNumber k)) : ∃ a₀ a₁ : A, r = TensorProduct.tmul k a₀ (1 : DualNumber k) + TensorProduct.tmul k a₁ DualNumber.eps := by
  refine TensorProduct.inductionOn r ?_ ?_
  ·
    intro a x
    refine ⟨x.fst • a, x.snd • a, ?_⟩
    conv_lhs => rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq x]
    rw [TensorProduct.tmul_add, DualNumber.inr_eq_smul_eps, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul]
    congr 1
    have : (TrivSqZeroExt.inl x.fst : (DualNumber k)) = x.fst • (1 : (DualNumber k)) := by
      rw [← TrivSqZeroExt.algebraMap_eq_inl, Algebra.algebraMap_eq_smul_one]
    rw [this, TensorProduct.tmul_smul]
  ·
    intro r s hr hs
    obtain ⟨a₀, a₁, rfl⟩ := hr
    obtain ⟨b₀, b₁, rfl⟩ := hs
    refine ⟨a₀ + b₀, a₁ + b₁, ?_⟩
    simp [TensorProduct.add_tmul]
    abel
private noncomputable def evalEps
  {k : Type u} [Field k] {A : Type u} [CommRing A] [Algebra k A]
  (y : AlgHom k A k) : AlgHom k (TensorProduct k A (DualNumber k)) (DualNumber k) :=
  Algebra.TensorProduct.lift ((Algebra.ofId k (DualNumber k)).comp y) (AlgHom.id k (DualNumber k)) (fun _ _ => .all _ _)
private lemma evalEps_tmul
  {k : Type u} [Field k] {A : Type u} [CommRing A] [Algebra k A]
  (y : AlgHom k A k) (a : A) (x : (DualNumber k)) : evalEps y (TensorProduct.tmul k a x) = y a • x := by
  simp [evalEps, Algebra.TensorProduct.lift_tmul, ← Algebra.smul_def]
private lemma tensor_eq_zero_of_forall_evalEps
  {k : Type u} [Field k] [IsAlgClosed k]
  {A : Type u} [CommRing A] [Algebra k A] [IsReduced A] [Algebra.FiniteType k A]
    (U : Set (PrimeSpectrum A)) (hUo : IsOpen U) (hU : Dense U) (r : TensorProduct k A (DualNumber k))
    (hr : ∀ m : PrimeSpectrum A, m ∈ U → ∀ y : AlgHom k A k, RingHom.ker (y : RingHom A k) = m.asIdeal → evalEps y r = 0) : r = 0 := by
  obtain ⟨a₀, a₁, rfl⟩ := exists_eq_tmul_one_add_tmul_eps r
  have key : ∀ m : PrimeSpectrum A, m ∈ U → ∀ y : AlgHom k A k, RingHom.ker (y : RingHom A k) = m.asIdeal → y a₀ = 0 ∧ y a₁ = 0 := by
    intro m hm y hy
    have h := hr m hm y hy
    rw [map_add, evalEps_tmul, evalEps_tmul] at h
    have h0 := congrArg TrivSqZeroExt.fst h
    have h1 := congrArg TrivSqZeroExt.snd h
    simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_smul, TrivSqZeroExt.fst_one, DualNumber.fst_eps, smul_eq_mul, mul_one, mul_zero, add_zero, TrivSqZeroExt.fst_zero, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_smul, TrivSqZeroExt.snd_one, DualNumber.snd_eps, zero_add, TrivSqZeroExt.snd_zero] at h0 h1
    exact ⟨h0, h1⟩
  have e0 : a₀ = 0 := eq_zero_of_forall_algHom U hUo hU a₀ (fun m hm y hy => (key m hm y hy).1)
  have e1 : a₁ = 0 := eq_zero_of_forall_algHom U hUo hU a₁ (fun m hm y hy => (key m hm y hy).2)
  simp [e0, e1]
private lemma chart_ht1
  {k : Type u} [Field k] {A : (CommRingCat : Type (u + 1))} [Algebra k A]
  {X : (Scheme : Type (u + 1))}
  (f : X ⟶ Spec (CommRingCat.of k))
  (a : Spec A ⟶ X)
  (y : AlgHom k A k)
  (g : Spec (CommRingCat.of (TensorProduct k A (DualNumber k))) ⟶
    pullback f (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))))
  (hg1 : g ≫ pullback.fst f _ =
    Spec.map (CommRingCat.ofHom (algebraMap A (TensorProduct k A (DualNumber k)))) ≫ a)
  (ψ : RingHom (TensorProduct k A (DualNumber k)) (DualNumber k))
  (hψ : ∀ z, ψ z = evalEps y z)
  (t : Spec (CommRingCat.of (DualNumber k)) ⟶
    Spec (CommRingCat.of (TensorProduct k A (DualNumber k))))
  (ht : t =
    Spec.map (CommRingCat.ofHom (R := TensorProduct k A (DualNumber k)) (S := (DualNumber k)) ψ)) :
  (t ≫ g) ≫ pullback.fst f _ =
    Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) ≫ Spec.map (CommRingCat.ofHom (y : RingHom A k)) ≫ a := by
  rw [Category.assoc, hg1, ← Category.assoc, ← Category.assoc, ht, ← Spec.map_comp, ← Spec.map_comp]
  congr 2
  rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 1
  refine RingHom.ext fun x => ?_
  simp only [RingHom.coe_comp, Function.comp_apply, hψ, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, evalEps_tmul, AlgHom.coe_toRingHom]
  rw [Algebra.algebraMap_eq_smul_one]
private lemma chart_ht2
  {k : Type u} [Field k] {A : (CommRingCat : Type (u + 1))} [Algebra k A]
  {X : (Scheme : Type (u + 1))}
  (f : X ⟶ Spec (CommRingCat.of k))
  (g : Spec (CommRingCat.of (TensorProduct k A (DualNumber k))) ⟶
    pullback f (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))))
  (hg2 : g ≫ pullback.snd f _ =
    Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight (R := k) (A := A) (B := (DualNumber k))).toRingHom))
  (y : AlgHom k A k)
  (ψ : RingHom (TensorProduct k A (DualNumber k)) (DualNumber k))
  (hψ : ∀ z, ψ z = evalEps y z)
  (t : Spec (CommRingCat.of (DualNumber k)) ⟶
    Spec (CommRingCat.of (TensorProduct k A (DualNumber k))))
  (ht : t =
    Spec.map (CommRingCat.ofHom (R := TensorProduct k A (DualNumber k)) (S := (DualNumber k)) ψ)) :
  (t ≫ g) ≫ pullback.snd f _ = 𝟙 _ := by
  rw [Category.assoc, hg2, ht, ← Spec.map_comp, ← Spec.map_id]
  congr 1
  rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_id]
  congr 1
  refine RingHom.ext fun x => ?_
  simp only [RingHom.coe_comp, Function.comp_apply, hψ, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Algebra.TensorProduct.includeRight_apply, evalEps_tmul, map_one, one_smul, RingHom.id_apply]
private lemma chart_hpt
  {k : Type u} [Field k] {A : (CommRingCat : Type (u + 1))} [Algebra k A]
  (y : AlgHom k A k)
  {X : (Scheme : Type (u + 1))}
  (a : Spec A ⟶ X)
  (U : X.Opens)
  (m : PrimeSpectrum A)
  (hm : m ∈ a.base ⁻¹' (U : Set X))
  (hy : RingHom.ker (y : RingHom A k) = m.asIdeal) :
  (Spec.map (CommRingCat.ofHom (y : RingHom A k)) ≫ a).base (closedPoint k) ∈ U := by
  have : (Spec.map (CommRingCat.ofHom (y : RingHom A k))).base (closedPoint k) = m := by
    apply PrimeSpectrum.ext
    change Ideal.comap (CommRingCat.ofHom (y : RingHom A k)).hom (maximalIdeal k) = m.asIdeal
    rw [CommRingCat.hom_ofHom, maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot, hy]
  show (Spec.map (CommRingCat.ofHom (y : RingHom A k)) ≫ a) (closedPoint k) ∈ U
  rw [Scheme.Hom.comp_apply]
  change a.base ((Spec.map (CommRingCat.ofHom (y : RingHom A k))).base (closedPoint k)) ∈ (U : Set X)
  rwa [this]
private lemma chart_eval_of_appTop
  {k : Type u} [Field k] {A : (CommRingCat : Type (u + 1))} [Algebra k A]
  (y : AlgHom k A k)
  (r : TensorProduct k A (DualNumber k))
  (ψ : RingHom (TensorProduct k A (DualNumber k)) (DualNumber k))
  (hψ : ∀ z, ψ z = evalEps y z)
  (t : Spec (CommRingCat.of (DualNumber k)) ⟶
    Spec (CommRingCat.of (TensorProduct k A (DualNumber k))))
  (ht : t =
    Spec.map (CommRingCat.ofHom (R := TensorProduct k A (DualNumber k)) (S := (DualNumber k)) ψ))
  (h0 : t.appTop ((Scheme.ΓSpecIso (.of (TensorProduct k A (DualNumber k)))).inv r) = 0) :
  evalEps y r = 0 := by
  have nat := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (R := TensorProduct k A (DualNumber k)) (S := (DualNumber k)) ψ)
  apply (map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of (DualNumber k))).inv).1).mp
  have e1 := congrArg (fun φ => φ.hom r) nat
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e1
  rw [← ht, hψ] at e1
  erw [e1]
  apply h0
private lemma chart_one_eval
  {k : Type u} [Field k] {X : (Scheme : Type (u + 1))}
  (f : X ⟶ Spec (CommRingCat.of k))
  (U : X.Opens)
  {A : (CommRingCat : Type (u + 1))} [Algebra k A]
  (a : Spec A ⟶ X)
  {Z : (Scheme : Type (u + 1))}
  (ι : Z ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))))) [IsClosedImmersion ι]
  (hι : ∀ y : AlgHom k A k, (Spec.map (CommRingCat.ofHom (y : RingHom A k)) ≫ a).base (closedPoint k) ∈ U → ∀ T : Spec (CommRingCat.of (DualNumber k)) ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))), T ≫ pullback.fst f _ = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) ≫ Spec.map (CommRingCat.ofHom (y : RingHom A k)) ≫ a → T ≫ pullback.snd f _ = 𝟙 _ → ∃ u : Spec (CommRingCat.of (DualNumber k)) ⟶ Z, u ≫ ι = T)
  (g : Spec (CommRingCat.of (TensorProduct k A (DualNumber k))) ⟶
    pullback f (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))))) [IsOpenImmersion g]
  (hg1 : g ≫ pullback.fst f _ = Spec.map (CommRingCat.ofHom (algebraMap A (TensorProduct k A (DualNumber k)))) ≫ a)
  (hg2 : g ≫ pullback.snd f _ = Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight (R := k) (A := A) (B := (DualNumber k))).toRingHom))
  (r : TensorProduct k A (DualNumber k))
  (hs : (pullback.fst g ι).appTop ((Scheme.ΓSpecIso (.of (TensorProduct k A (DualNumber k)))).inv r) = 0)
  (m : PrimeSpectrum A)
  (hm : m ∈ a.base ⁻¹' (U : Set X))
  (y : AlgHom k A k)
  (hy : RingHom.ker (y : RingHom A k) = m.asIdeal) :
  evalEps y r = 0 := by
  let ψ : RingHom (TensorProduct k A (DualNumber k)) (DualNumber k) := (evalEps y).toRingHom
  have hψ : ∀ z, ψ z = evalEps y z := fun _ => rfl
  set t : Spec (CommRingCat.of (DualNumber k)) ⟶ Spec (CommRingCat.of (TensorProduct k A (DualNumber k))) :=
    Spec.map (CommRingCat.ofHom (R := TensorProduct k A (DualNumber k)) (S := (DualNumber k)) ψ) with ht
  obtain ⟨u, hu⟩ := hι y (chart_hpt y a U m hm hy) (t ≫ g)
    (chart_ht1 f a y g hg1 ψ hψ t ht) (chart_ht2 f g hg2 y ψ hψ t ht)
  let v : Spec (CommRingCat.of (DualNumber k)) ⟶ pullback g ι := pullback.lift t u hu.symm
  have hv : v ≫ pullback.fst g ι = t := pullback.lift_fst _ _ _
  apply chart_eval_of_appTop y r ψ hψ t ht
  have hs' : (pullback.fst g ι).appTop ((Scheme.ΓSpecIso (.of (TensorProduct k A (DualNumber k)))).inv r) = 0 := hs
  rw [← hv, Scheme.Hom.comp_appTop]
  change v.appTop ((pullback.fst g ι).appTop _) = 0
  rw [hs', map_zero]
private lemma chart_section_zero
  {k : Type u} [Field k] [IsAlgClosed k] {X : (Scheme : Type (u + 1))}
  (f : X ⟶ Spec (CommRingCat.of k))
  (U : X.Opens) (hU : Dense (U : Set X))
  {A : (CommRingCat : Type (u + 1))} [Algebra k A] [IsReduced A] [Algebra.FiniteType k A]
  (a : Spec A ⟶ X) [IsOpenImmersion a]
  {Z : (Scheme : Type (u + 1))}
  (ι : Z ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))))) [IsClosedImmersion ι]
  (hι : ∀ y : AlgHom k A k, (Spec.map (CommRingCat.ofHom (y : RingHom A k)) ≫ a).base (closedPoint k) ∈ U → ∀ T : Spec (CommRingCat.of (DualNumber k)) ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))), T ≫ pullback.fst f _ = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) ≫ Spec.map (CommRingCat.ofHom (y : RingHom A k)) ≫ a → T ≫ pullback.snd f _ = 𝟙 _ → ∃ u : Spec (CommRingCat.of (DualNumber k)) ⟶ Z, u ≫ ι = T)
  (g : Spec (CommRingCat.of (TensorProduct k A (DualNumber k))) ⟶
    pullback f (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))))) [IsOpenImmersion g]
  (hg1 : g ≫ pullback.fst f _ = Spec.map (CommRingCat.ofHom (algebraMap A (TensorProduct k A (DualNumber k)))) ≫ a)
  (hg2 : g ≫ pullback.snd f _ = Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight (R := k) (A := A) (B := (DualNumber k))).toRingHom))
  (r : TensorProduct k A (DualNumber k))
  (hs : (pullback.fst g ι).appTop ((Scheme.ΓSpecIso (.of (TensorProduct k A (DualNumber k)))).inv r) = 0) :
  r = 0 := by
  refine tensor_eq_zero_of_forall_evalEps (k := k) (A := A) (a.base ⁻¹' (U : Set X))
    (U.isOpen.preimage a.continuous) (hU.preimage a.isOpenEmbedding.isOpenMap) r ?_
  intro m hm y hy
  apply chart_one_eval f U a ι hι g hg1 hg2 r hs m hm y hy
private lemma chart_of_appTop
  {k : Type u} [Field k] [IsAlgClosed k] {X : (Scheme : Type (u + 1))}
  (f : X ⟶ Spec (CommRingCat.of k))
  (U : X.Opens) (hU : Dense (U : Set X))
  {A : (CommRingCat : Type (u + 1))} [Algebra k A] [IsReduced A] [Algebra.FiniteType k A]
  (a : Spec A ⟶ X) [IsOpenImmersion a]
  {Z : (Scheme : Type (u + 1))}
  (ι : Z ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))))) [IsClosedImmersion ι]
  (hι : ∀ y : AlgHom k A k, (Spec.map (CommRingCat.ofHom (y : RingHom A k)) ≫ a).base (closedPoint k) ∈ U → ∀ T : Spec (CommRingCat.of (DualNumber k)) ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))), T ≫ pullback.fst f _ = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) ≫ Spec.map (CommRingCat.ofHom (y : RingHom A k)) ≫ a → T ≫ pullback.snd f _ = 𝟙 _ → ∃ u : Spec (CommRingCat.of (DualNumber k)) ⟶ Z, u ≫ ι = T)
  (g : Spec (CommRingCat.of (TensorProduct k A (DualNumber k))) ⟶
    pullback f (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))))) [IsOpenImmersion g]
  (hg1 : g ≫ pullback.fst f _ = Spec.map (CommRingCat.ofHom (algebraMap A (TensorProduct k A (DualNumber k)))) ≫ a)
  (hg2 : g ≫ pullback.snd f _ = Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight (R := k) (A := A) (B := (DualNumber k))).toRingHom))
  (s : ↑((Spec (CommRingCat.of (TensorProduct k A (DualNumber k)))).presheaf.obj (op ⊤)))
  (hs : (pullback.fst g ι).appTop s = 0) :
  s = 0 := by
  obtain ⟨r, rfl⟩ : ∃ r, s = (Scheme.ΓSpecIso (.of (TensorProduct k A (DualNumber k)))).inv r :=
    ⟨(Scheme.ΓSpecIso (.of (TensorProduct k A (DualNumber k)))).hom s, (Iso.hom_inv_id_apply (Scheme.ΓSpecIso (.of (TensorProduct k A (DualNumber k)))) s).symm⟩
  suffices hr : r = 0 by simp [hr]
  apply chart_section_zero f U hU a ι hι g hg1 hg2 r hs
private lemma chart_fst_ker
  {k : Type u} [Field k] [IsAlgClosed k] {X : (Scheme : Type (u + 1))}
  (f : X ⟶ Spec (CommRingCat.of k)) [IsReduced X]
    (U : X.Opens) (hU : Dense (U : Set X))
    {A : (CommRingCat : Type (u + 1))} [Algebra k A] [IsReduced A] [Algebra.FiniteType k A]
    (a : Spec A ⟶ X) [IsOpenImmersion a]
    {Z : (Scheme : Type (u + 1))}
    (ι : Z ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))))) [IsClosedImmersion ι]
    (hι : ∀ y : AlgHom k A k, (Spec.map (CommRingCat.ofHom (y : RingHom A k)) ≫ a).base (closedPoint k) ∈ U → ∀ T : Spec (CommRingCat.of (DualNumber k)) ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))), T ≫ pullback.fst f _ = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) ≫ Spec.map (CommRingCat.ofHom (y : RingHom A k)) ≫ a → T ≫ pullback.snd f _ = 𝟙 _ → ∃ u : Spec (CommRingCat.of (DualNumber k)) ⟶ Z, u ≫ ι = T)
    (g : Spec (CommRingCat.of (TensorProduct k A (DualNumber k))) ⟶
      pullback f (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))))) [IsOpenImmersion g]
    (hg1 : g ≫ pullback.fst f _ = Spec.map (CommRingCat.ofHom (algebraMap A (TensorProduct k A (DualNumber k)))) ≫ a)
    (hg2 : g ≫ pullback.snd f _ = Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight (R := k) (A := A) (B := (DualNumber k))).toRingHom)) :
  (pullback.fst g ι).ker.ideal ⟨⊤, isAffineOpen_top _⟩ = ⊥ := by
  apply eq_bot_iff.mpr
  intro s hs
  have hs0 := Scheme.Hom.ideal_ker_le (pullback.fst g ι) ⟨⊤, isAffineOpen_top _⟩ hs
  rw [RingHom.mem_ker] at hs0
  apply chart_of_appTop f U hU a ι hι g hg1 hg2 s hs0

private lemma chart
  {k : Type u} [Field k] [IsAlgClosed k] {X : (Scheme : Type (u + 1))}
  (f : X ⟶ Spec (CommRingCat.of k)) [IsReduced X]
    (U : X.Opens) (hU : Dense (U : Set X))
    {A : (CommRingCat : Type (u + 1))} [Algebra k A] [IsReduced A] [Algebra.FiniteType k A]
    (a : Spec A ⟶ X) [IsOpenImmersion a]
    {Z : (Scheme : Type (u + 1))}
    (ι : Z ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))))) [IsClosedImmersion ι]
    (hι : ∀ y : AlgHom k A k, (Spec.map (CommRingCat.ofHom (y : RingHom A k)) ≫ a).base (closedPoint k) ∈ U → ∀ T : Spec (CommRingCat.of (DualNumber k)) ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))), T ≫ pullback.fst f _ = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) ≫ Spec.map (CommRingCat.ofHom (y : RingHom A k)) ≫ a → T ≫ pullback.snd f _ = 𝟙 _ → ∃ u : Spec (CommRingCat.of (DualNumber k)) ⟶ Z, u ≫ ι = T)
    (g : Spec (CommRingCat.of (TensorProduct k A (DualNumber k))) ⟶
      pullback f (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))))) [IsOpenImmersion g]
    (hg1 : g ≫ pullback.fst f _ = Spec.map (CommRingCat.ofHom (algebraMap A (TensorProduct k A (DualNumber k)))) ≫ a)
    (hg2 : g ≫ pullback.snd f _ = Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight (R := k) (A := A) (B := (DualNumber k))).toRingHom)) :
    ι.ker.ideal ⟨(Scheme.Hom.opensFunctor g).obj ⊤, (isAffineOpen_top _).image_of_isOpenImmersion g⟩ = ⊥ := by
  classical
  have H := IsPullback.of_hasPullback g ι
  have hker := Scheme.ker_ideal_of_isPullback_of_isOpenImmersion ι (pullback.fst g ι)
    (pullback.snd g ι) g H ⟨⊤, isAffineOpen_top _⟩
  suffices h : (pullback.fst g ι).ker.ideal ⟨⊤, isAffineOpen_top _⟩ = ⊥ by
    rw [hker] at h
    have hsurj : Function.Surjective (g.appIso ⊤).inv.hom :=
      (ConcreteCategory.bijective_of_isIso (g.appIso ⊤).inv).2
    have e := Ideal.map_comap_of_surjective (g.appIso ⊤).inv.hom hsurj
      (ι.ker.ideal ⟨(Scheme.Hom.opensFunctor g).obj ⊤, (isAffineOpen_top _).image_of_isOpenImmersion g⟩)
    rw [← e, h, Ideal.map_bot]
  apply chart_fst_ker f U hU a ι hι g hg1 hg2
private lemma dense_main
  (k : Type u) [Field k] [IsAlgClosed k] {X Y S : (Scheme : Type (u + 1))} (f : X ⟶ Spec (CommRingCat.of k))
    [IsReduced X] [LocallyOfFiniteType f]
    (F G : pullback f (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))) ⟶ Y)
    (i : Y ⟶ S) [IsSeparated i] (hFG : F ≫ i = G ≫ i)
    (U : X.Opens) (hU : Dense (U : Set ↥X))
    (h : ∀ (y : Spec (CommRingCat.of k) ⟶ X), y ≫ f = 𝟙 _ → y.base (IsLocalRing.closedPoint k) ∈ U → ∀ (T : Spec (CommRingCat.of (DualNumber k)) ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))))), T ≫ pullback.fst f _ = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) ≫ y → T ≫ pullback.snd f _ = 𝟙 _ → T ≫ F = T ≫ G) :
    F = G := by
  classical
  let X' : Over S := Over.mk (F ≫ i)
  let Y' : Over S := Over.mk i
  let F' : X' ⟶ Y' := Over.homMk F rfl
  let G' : X' ⟶ Y' := Over.homMk G hFG.symm
  let _ : IsSeparated Y'.hom := ‹IsSeparated i›
  let ι : (equalizer F' G').left ⟶ pullback f _ := (equalizer.ι F' G').left
  let hιc : IsClosedImmersion ι := AlgebraicGeometry.isClosedImmersion_equalizer_ι_left F' G'
  suffices IsIso ι by
    have hc := congrArg Over.Hom.left (equalizer.condition F' G')
    simp only [Over.comp_left, Over.homMk_left, F', G'] at hc
    rwa [← cancel_epi ι]
  rw [IsClosedImmersion.isIso_iff_ker_eq_bot]
  have hfac : ∀ {W : (Scheme : Type (u + 1))} (T : W ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))))), T ≫ F = T ≫ G → ∃ u : W ⟶ (equalizer F' G').left, u ≫ ι = T := by
    intro W T hT
    let W' : Over S := Over.mk (T ≫ F ≫ i)
    let T' : W' ⟶ X' := Over.homMk T rfl
    have hT' : T' ≫ F' = T' ≫ G' := by
      ext
      simp [Over.comp_left] at hT ⊢
      apply hT
    refine ⟨(equalizer.lift T' hT').left, ?_⟩
    have := congrArg Over.Hom.left (equalizer.lift_ι T' hT')
    simp only [Over.comp_left] at this
    exact this
  let 𝒰 := X.affineOpenCover
  let inst : ∀ j : 𝒰.I₀, Algebra k (𝒰.X j) := fun j => (Spec.preimage (𝒰.f j ≫ f)).hom.toAlgebra
  have hspec : ∀ j, 𝒰.f j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k (𝒰.X j))) := fun j => by
    rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, Spec.map_preimage]
  let 𝒱₀ := Scheme.Pullback.openCoverOfLeft 𝒰.openCover f
    (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))))
  let e₂ : ∀ j : 𝒰.I₀, Spec (CommRingCat.of (TensorProduct k (𝒰.X j) (DualNumber k))) ≅
    pullback (𝒰.f j ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))) := fun j =>
    (pullbackSpecIso k (𝒰.X j) (DualNumber k)).symm.trans (pullback.congrHom (hspec j).symm rfl)
  have he1 : ∀ j, (e₂ j).hom ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap (𝒰.X j) (TensorProduct k (𝒰.X j) (DualNumber k)))) := by
    intro j
    simp only [e₂, Iso.trans_hom, Iso.symm_hom, pullback.congrHom_hom, Category.assoc]
    erw [pullback.lift_fst]
    rw [Category.comp_id, pullbackSpecIso_inv_fst']
  have he2 : ∀ j, (e₂ j).hom ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := k) (A := 𝒰.X j) (B := (DualNumber k))).toRingHom) := by
    intro j
    simp only [e₂, Iso.trans_hom, Iso.symm_hom, pullback.congrHom_hom, Category.assoc]
    erw [pullback.lift_snd]
    rw [Category.comp_id, pullbackSpecIso_inv_snd]
    rfl
  have hf1 : ∀ j, 𝒱₀.f j ≫ pullback.fst f _ = pullback.fst _ _ ≫ 𝒰.f j := by
    intro j
    show (Scheme.Pullback.openCoverOfLeft 𝒰.openCover f _).f j ≫ _ = _
    rw [Scheme.Pullback.openCoverOfLeft_f]
    exact pullback.lift_fst _ _ _
  have hf2 : ∀ j, 𝒱₀.f j ≫ pullback.snd f _ = pullback.snd _ _ := by
    intro j
    show (Scheme.Pullback.openCoverOfLeft 𝒰.openCover f _).f j ≫ _ = _
    rw [Scheme.Pullback.openCoverOfLeft_f]
    exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  let 𝒱 : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))))).OpenCover :=
    𝒱₀.copy 𝒰.I₀ (fun j => Spec (CommRingCat.of (TensorProduct k (𝒰.X j) (DualNumber k))))
    (fun j => (e₂ j).hom ≫ 𝒱₀.f j) (Equiv.refl _) e₂ (fun _ => rfl)
  have hVf : ∀ j, 𝒱.f j = (e₂ j).hom ≫ 𝒱₀.f j := fun _ => rfl
  have hg1 : ∀ j, ((e₂ j).hom ≫ 𝒱₀.f j) ≫ pullback.fst f _ =
      Spec.map (CommRingCat.ofHom (algebraMap (𝒰.X j) (TensorProduct k (𝒰.X j) (DualNumber k)))) ≫ 𝒰.f j := by
    intro j
    rw [Category.assoc]
    erw [hf1 j]
    erw [← Category.assoc, he1 j]
  have hg2 : ∀ j, ((e₂ j).hom ≫ 𝒱₀.f j) ≫ pullback.snd f _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := k) (A := 𝒰.X j) (B := (DualNumber k))).toRingHom) := by
    intro j
    rw [Category.assoc]
    erw [hf2 j]
    erw [he2 j]
  let hVaff : ∀ j, IsAffine (𝒱.X j) := fun j =>
    (inferInstance : IsAffine (Spec (CommRingCat.of (TensorProduct k (𝒰.X j) (DualNumber k)))))
  let hVopen : ∀ j, IsOpenImmersion ((e₂ j).hom ≫ 𝒱₀.f j) := fun j =>
    (inferInstance : IsOpenImmersion (𝒱.f j))
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun j => ⟨(Scheme.Hom.opensFunctor (𝒱.f j)).obj ⊤, (isAffineOpen_top (𝒱.X j)).image_of_isOpenImmersion (𝒱.f j)⟩) ?_ ?_
  ·
    change ⨆ j, (Scheme.Hom.opensFunctor (𝒱.f j)).obj ⊤ = ⊤
    simp only [Scheme.Hom.image_top_eq_opensRange]
    apply 𝒱.iSup_opensRange
  intro j
  rw [Scheme.IdealSheafData.ideal_bot, Pi.bot_apply]
  let _ : IsReduced (𝒰.X j) := by
    have : IsReduced (Spec (𝒰.X j)) := isReduced_of_isOpenImmersion (𝒰.f j)
    exact (affine_isReduced_iff (𝒰.X j)).mp this
  let _ : Algebra.FiniteType k (𝒰.X j) := by
    have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k (𝒰.X j)))) := by
      rw [← hspec j]
      infer_instance
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at this
    exact RingHom.finiteType_algebraMap.mp this
  show ι.ker.ideal ⟨(Scheme.Hom.opensFunctor ((e₂ j).hom ≫ 𝒱₀.f j)).obj ⊤, _⟩ = ⊥
  refine chart f U hU (A := 𝒰.X j) (a := 𝒰.f j) ι ?_ ((e₂ j).hom ≫ 𝒱₀.f j) (hg1 j) (hg2 j)
  intro y hy T hT1 hT2
  refine hfac T (h _ ?_ hy T hT1 hT2)
  rw [Category.assoc, hspec j, ← Spec.map_comp, ← Spec.map_id]
  congr 1
  rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_id]
  congr 1
  exact y.comp_algebraMap
/--
[AlgebraicGeometry_Scheme_Hom_eq_of_forall_section_comp_eq_of_dense_of_dualNumber](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_eq_of_forall_section_comp_eq_of_dense_of_dualNumber.lean)
-/
@[path]
private lemma main
  (k : Type u) [Field k] [IsAlgClosed k] {X Y S : (Scheme : Type (u + 1))} (f : X ⟶ Spec (CommRingCat.of k))
    [IsReduced X] [LocallyOfFiniteType f]
    (F G : pullback f (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))) ⟶ Y)
    (i : Y ⟶ S) [IsSeparated i] (hFG : F ≫ i = G ≫ i)
    (U : X.Opens) (hU : Dense (U : Set ↥X))
    (h : ∀ (y : Spec (CommRingCat.of k) ⟶ X), y ≫ f = 𝟙 _ → y.base (IsLocalRing.closedPoint k) ∈ U → ∀ (T : Spec (CommRingCat.of (DualNumber k)) ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))))), T ≫ pullback.fst f _ = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) ≫ y → T ≫ pullback.snd f _ = 𝟙 _ → T ≫ F = T ≫ G) :
    F = G := by
  apply dense_main k f F G i hFG U hU h


-- created on 2026-10-20
