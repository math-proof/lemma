import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u v w

private lemma algebraMap_quotient_bijective
  {K : Type u} [Field K] [IsAlgClosed K]
  {A : Type v} [CommRing A] [Algebra K A] [Algebra.FiniteType K A]
  (m : Ideal A) [m.IsMaximal] :
  -- imply
  Function.Bijective (algebraMap K (A ⧸ m)) := by
  -- proof
  let _ : Field (A ⧸ m) := Ideal.Quotient.field m
  have : Module.Finite K (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing K (A ⧸ m)
  have : Algebra.IsIntegral K (A ⧸ m) := inferInstance
  apply IsAlgClosed.algebraMap_bijective_of_isIntegral

private noncomputable def pointOfMaximal
  {K : Type u} [Field K] [IsAlgClosed K]
  {A : Type v} [CommRing A] [Algebra K A] [Algebra.FiniteType K A]
  (m : Ideal A) [m.IsMaximal] :
  AlgHom K A K :=
  let e := RingEquiv.ofBijective (algebraMap K (A ⧸ m)) (algebraMap_quotient_bijective m)
  { toRingHom := e.symm.toRingHom.comp (Ideal.Quotient.mk m)
    commutes' := fun k => by
      change e.symm (Ideal.Quotient.mk m (algebraMap K A k)) = k
      rw [Ideal.Quotient.mk_algebraMap]
      apply e.symm_apply_apply k }

private lemma pointOfMaximal_eq_zero_iff
  {K : Type u} [Field K] [IsAlgClosed K]
  {A : Type v} [CommRing A] [Algebra K A] [Algebra.FiniteType K A]
  (m : Ideal A) [m.IsMaximal]
  (a : A) :
  -- imply
  pointOfMaximal (K := K) m a = 0 ↔ a ∈ m := by
  -- proof
  change (RingEquiv.ofBijective (algebraMap K (A ⧸ m)) (algebraMap_quotient_bijective m)).symm
    (Ideal.Quotient.mk m a) = 0 ↔ a ∈ m
  rw [map_eq_zero_iff _ (RingEquiv.injective _), Ideal.Quotient.eq_zero_iff_mem]

private lemma isDomain_tensorProduct_of_finiteType
  {K : Type u} [Field K] [IsAlgClosed K]
  (A : Type v) [CommRing A] [Algebra K A] [Algebra.FiniteType K A] [IsDomain A]
  (B : Type w) [CommRing B] [Algebra K B] [IsDomain B] :
  -- imply
  IsDomain (TensorProduct K A B) := by
  -- proof
  classical
  let _ : Nontrivial (TensorProduct K A B) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain K A B
      (algebraMap K A).injective (algebraMap K B).injective
  let bB := Module.Free.chooseBasis K B
  let 𝔅 := Algebra.TensorProduct.basis A bB
  let I : TensorProduct K A B → Ideal A := fun x => Ideal.span (Set.range (𝔅.repr x))
  have hI : ∀ x, I x = ⊥ → x = 0 := by
    intro x hx
    apply 𝔅.repr.injective
    rw [map_zero]
    ext i
    apply (Ideal.span_eq_bot.mp hx) _ ⟨i, rfl⟩
  have hpt : ∀ (x y : TensorProduct K A B), x * y = 0 → ∀ (m : Ideal A) [m.IsMaximal], I x ≤ m ∨ I y ≤ m := by
    intro x y hxy m _
    let φ : AlgHom K A K := pointOfMaximal m
    let ψ : AlgHom K (TensorProduct K A B) B :=
      Algebra.TensorProduct.lift ((Algebra.ofId K B).comp φ) (AlgHom.id K B) (fun _ _ => Commute.all _ _)
    have hψ : ∀ (z : TensorProduct K A B) i, bB.repr (ψ z) i = φ (𝔅.repr z i) := by
      intro z i
      induction z using TensorProduct.inductionOn with
      | tmul a b =>
        simp only [ψ, 𝔅, Algebra.TensorProduct.lift_tmul, AlgHom.coe_comp, Function.comp_apply, Algebra.ofId_apply, AlgHom.coe_id, id_eq, Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, map_mul, AlgHom.commutes]
        rw [← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul, Algebra.algebraMap_self, RingHom.id_apply]
      | add z w hz hw =>
        simp [map_add, hz, hw]
    have hker : ∀ z : TensorProduct K A B, ψ z = 0 → I z ≤ m := by
      intro z hz
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, ← pointOfMaximal_eq_zero_iff (K := K), ← hψ, hz, map_zero, Finsupp.zero_apply]
    have h0 : ψ x * ψ y = 0 := by
      rw [← map_mul, hxy, map_zero]
    obtain h | h := mul_eq_zero.mp h0
    · apply Or.inl (hker x h)
    · apply Or.inr (hker y h)
  let _ : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := K) (B := A)
  refine @NoZeroDivisors.to_isDomain _ _ _ ⟨fun {x y} hxy => ?_⟩
  have hle : I x * I y ≤ (⊥ : Ideal A) := by
    rw [← Ideal.radical_bot_of_isReduced, Ideal.radical_eq_jacobson]
    refine le_sInf ?_
    rintro J ⟨-, hJ⟩
    obtain h | h := hpt x y hxy J
    · apply Ideal.mul_le_left.trans h
    · apply Ideal.mul_le_right.trans h
  obtain h | h := Ideal.mul_eq_bot.mp (le_bot_iff.mp hle)
  · apply Or.inl (hI x h)
  · apply Or.inr (hI y h)

private lemma isDomain_tensorProduct_of_field
  (k : Type u) [Field k] [IsAlgClosed k]
  (F : Type v) [Field F] [Algebra k F]
  (B : Type w) [CommRing B] [Algebra k B] [IsDomain B] :
  -- imply
  IsDomain (TensorProduct k F B) := by
  -- proof
  classical
  let _ : Nontrivial (TensorProduct k F B) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain k F B
      (algebraMap k F).injective (algebraMap k B).injective
  refine @NoZeroDivisors.to_isDomain _ _ _ ⟨fun {x y} hxy => ?_⟩
  obtain ⟨sx, hx⟩ := TensorProduct.exists_finset x
  obtain ⟨sy, hy⟩ := TensorProduct.exists_finset y
  let s0 := sx.image Prod.fst ∪ sy.image Prod.fst
  let A : Subalgebra k F := Algebra.adjoin k (↑s0 : Set F)
  let _ : Algebra.FiniteType k A := A.fg_iff_finiteType.mp ⟨s0, rfl⟩
  let ι : AlgHom k (TensorProduct k A B) (TensorProduct k F B) :=
    Algebra.TensorProduct.map A.val (AlgHom.id k B)
  have hι : Function.Injective ι := by
    have h : Function.Injective (A.val.toLinearMap.rTensor B) :=
      Module.Flat.rTensor_preserves_injective_linearMap (M := B) A.val.toLinearMap Subtype.val_injective
    intro a b hab
    apply h hab
  have hlift : ∀ s : Finset (F × B), (∀ p ∈ s, p.1 ∈ A) → ∃ z : TensorProduct k A B, ι z = ∑ p ∈ s, TensorProduct.tmul k p.1 p.2 := by
    intro s hs
    refine ⟨∑ p ∈ s.attach, TensorProduct.tmul k (⟨p.1.1, hs p.1 p.2⟩ : A) p.1.2, ?_⟩
    rw [map_sum, ← Finset.sum_attach s]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp [ι]
  have hxA : ∀ p ∈ sx, p.1 ∈ A := fun p hp =>
    Algebra.subset_adjoin (Finset.mem_coe.mpr (Finset.mem_union_left _ (Finset.mem_image_of_mem Prod.fst hp)))
  have hyA : ∀ p ∈ sy, p.1 ∈ A := fun p hp =>
    Algebra.subset_adjoin (Finset.mem_coe.mpr (Finset.mem_union_right _ (Finset.mem_image_of_mem Prod.fst hp)))
  obtain ⟨x', hx'⟩ := hlift sx hxA
  obtain ⟨y', hy'⟩ := hlift sy hyA
  rw [← hx] at hx'
  rw [← hy] at hy'
  subst hx' hy'
  let _ : IsDomain (TensorProduct k A B) := isDomain_tensorProduct_of_finiteType A B
  have hxy' : x' * y' = 0 := hι (by rw [map_mul, hxy, map_zero])
  obtain h | h := mul_eq_zero.mp hxy'
  · apply Or.inl (by rw [h, map_zero])
  · apply Or.inr (by rw [h, map_zero])

private lemma irreducibleSpace_fiber_fst
  {k : Type u} [Field k] [IsAlgClosed k]
  {X : (Scheme : Type (u + 1))}
  (f : X ⟶ Spec (CommRingCat.of k))
  (K : Type u) [Field K] [Algebra k K]
  (x : X) :
  -- imply
  let Y := (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).fiber x
  IrreducibleSpace ↥Y := by
  -- proof
  set i : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k K)) with hi
  let g := X.fromSpecResidueField x
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (g ≫ f)
  algebraize [φ.hom]
  let Y := (pullback.fst f i).fiber x
  let S := Spec (CommRingCat.of (TensorProduct k (X.residueField x) K))
  let e : Y ≅ S :=
    (((pullbackSymmetry (pullback.fst f i) g).trans (pullbackRightPullbackFstIso f i g)).trans
      (pullback.congrHom hφ.symm rfl)).trans (pullbackSpecIso k (X.residueField x) K)
  let _ : IsDomain (TensorProduct k (X.residueField x) K) :=
    isDomain_tensorProduct_of_field k (X.residueField x) K
  let _ : IrreducibleSpace ↥S :=
    inferInstanceAs (IrreducibleSpace (PrimeSpectrum (TensorProduct k (X.residueField x) K)))
  apply e.hom.homeomorph.irreducibleSpace_iff.mpr inferInstance

private lemma irreducibleSpace_pullback
  {k : Type u} [Field k] [IsAlgClosed k]
  {X : (Scheme : Type (u + 1))} [IrreducibleSpace X]
  (f : X ⟶ Spec (CommRingCat.of k))
  (K : Type u) [Field K] [Algebra k K] :
  -- imply
  let Z := pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  IrreducibleSpace ↥Z := by
  -- proof
  set i : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k K)) with hi
  let Sk := Spec (CommRingCat.of k)
  let _ : Subsingleton ↥Sk := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  let _ : IsIntegral (Spec (CommRingCat.of k)) := inferInstance
  let _ : Surjective i := ⟨fun _ => ⟨IsLocalRing.closedPoint K, Subsingleton.elim _ _⟩⟩
  let _ : Surjective (pullback.fst f i) := MorphismProperty.pullback_fst f i inferInstance
  have hopen : IsOpenMap (pullback.fst f i) := (pullback.fst f i).isOpenMap
  have hsurj : Function.Surjective (pullback.fst f i) := (pullback.fst f i).surjective
  rw [irreducibleSpace_def, Set.top_eq_univ, ← Set.preimage_univ (f := (pullback.fst f i))]
  refine (IrreducibleSpace.isIrreducible_univ X).preimage_of_isPreirreducible_fiber
    (pullback.fst f i) hopen (fun x => ?_) ?_
  ·
    rw [← Scheme.Hom.range_fiberι, ← Set.image_univ]
    let _ := irreducibleSpace_fiber_fst f K x
    apply ((IrreducibleSpace.isIrreducible_univ _).image _
      ((pullback.fst f i).fiberι x).continuous.continuousOn).isPreirreducible
  ·
    obtain ⟨x⟩ := (inferInstance : Nonempty X)
    obtain ⟨z, hz⟩ := hsurj x
    refine ⟨x, Set.mem_univ x, z, hz⟩

/--
[AlgebraicGeometry_GeometricallyIrreducible_of_irreducibleSpace_of_isAlgClosed](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_GeometricallyIrreducible_of_irreducibleSpace_of_isAlgClosed.lean)
-/
@[path]
private lemma main
  {k : Type u} [Field k] [IsAlgClosed k]
  {X : (Scheme : Type (u + 1))} [IrreducibleSpace X]
  {f : X ⟶ Spec (CommRingCat.of k)} :
  -- imply
  GeometricallyIrreducible f := by
  -- proof
  refine ⟨(geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms
    (P := fun Y : (Scheme : Type (u + 1)) => IrreducibleSpace Y)).mpr fun K _ _ => ?_⟩
  apply irreducibleSpace_pullback f K


-- created on 2026-10-20
