import Mathlib
import Initialize.Tactic.Attr.Basic
open Polynomial
open scoped TensorProduct


private lemma map_maximalIdeal_le_of_isMaximal
  [CommRing R] [IsLocalRing R] [CommRing A] [Algebra R A] [Module.Finite R A]
  (𝔫 : Ideal A) [𝔫.IsMaximal] :
-- imply
  (IsLocalRing.maximalIdeal R).map (algebraMap R A) ≤ 𝔫 := by
-- proof
  have : Algebra.IsIntegral R A := Algebra.IsIntegral.of_finite R A
  rw [Ideal.map_le_iff_le_comap]
  have : (𝔫.comap (algebraMap R A)).IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal 𝔫
  apply (IsLocalRing.eq_maximalIdeal inferInstance).ge


private lemma isUnit_one_add_of_mem_map_maximalIdeal
  [CommRing R] [IsLocalRing R] [CommRing A] [Algebra R A] [Module.Finite R A]
  {x : A}
-- given
  (hx : x ∈ (IsLocalRing.maximalIdeal R).map (algebraMap R A)) :
-- imply
  IsUnit (1 + x) := by
-- proof
  have hj : x ∈ (⊥ : Ideal A).jacobson := by
    rw [Ideal.jacobson, Ideal.mem_sInf]
    rintro 𝔫 ⟨-, h𝔫⟩
    have := h𝔫
    apply map_maximalIdeal_le_of_isMaximal 𝔫 hx
  have := Ideal.mem_jacobson_bot.mp hj 1
  rwa [mul_one, add_comm] at this


private lemma exists_derivative_mul_add_mul_eq_one
  {R : Type u} [CommRing R] [IsLocalRing R]
  (p : R[X])
-- given
  (hp : p.Monic)
  (hsep : (p.map (IsLocalRing.residue R)).Separable) :
-- imply
  ∃ p₁ p₂ : R[X], derivative p * p₁ + p * p₂ = 1 := by
-- proof
  obtain ⟨abar, bbar, hab⟩ := hsep
  obtain ⟨a, rfl⟩ := map_surjective (IsLocalRing.residue R) IsLocalRing.residue_surjective abar
  obtain ⟨b, rfl⟩ := map_surjective (IsLocalRing.residue R) IsLocalRing.residue_surjective bbar
  set q : R[X] := a * p + b * derivative p - 1 with hq
  have hqmap : q.map (IsLocalRing.residue R) = 0 := by
    rw [hq, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, ← derivative_map, hab, Polynomial.map_one, sub_self]
  have : Module.Finite R (AdjoinRoot p) := (AdjoinRoot.powerBasis' hp).finite
  have hqmem : AdjoinRoot.mk p q ∈ (IsLocalRing.maximalIdeal R).map (algebraMap R (AdjoinRoot p)) := by
    have hC : q ∈ (IsLocalRing.maximalIdeal R).map (C : R →+* R[X]) := by
      rw [Ideal.mem_map_C_iff]
      intro n
      have := congrArg (fun r => r.coeff n) hqmap
      simp only [coeff_map, coeff_zero] at this
      apply (IsLocalRing.residue_eq_zero_iff _).mp this
    rw [AdjoinRoot.algebraMap_eq, show (AdjoinRoot.of p) = (AdjoinRoot.mk p).comp C from rfl, ← Ideal.map_map]
    apply Ideal.mem_map_of_mem _ hC
  obtain ⟨u, hu⟩ := isUnit_one_add_of_mem_map_maximalIdeal hqmem
  have hb : AdjoinRoot.mk p (b * derivative p) = 1 + AdjoinRoot.mk p q := by
    simp [hq, map_sub, map_add, map_mul, map_one, AdjoinRoot.mk_self, mul_zero, zero_add, add_sub_cancel]
  obtain ⟨c, hc⟩ := AdjoinRoot.mk_surjective (AdjoinRoot.mk p b * (↑u⁻¹ : AdjoinRoot p))
  have h1 : AdjoinRoot.mk p (derivative p * c - 1) = 0 := by
    rw [map_sub, map_one, map_mul, hc, ← mul_assoc, mul_comm (AdjoinRoot.mk p (derivative p)) (AdjoinRoot.mk p b),
      ← map_mul, hb, ← hu, Units.mul_inv, sub_self]
  obtain ⟨d, hd⟩ := (AdjoinRoot.mk_eq_zero).mp h1
  refine ⟨c, -d, ?_⟩
  linear_combination hd


private lemma etale_adjoinRoot
  {R : Type u} [CommRing R] [IsLocalRing R]
  (p : R[X])
-- given
  (hp : p.Monic)
  (hsep : (p.map (IsLocalRing.residue R)).Separable) :
-- imply
  Algebra.Etale R (AdjoinRoot p) := by
-- proof
  obtain ⟨p₁, p₂, h⟩ := exists_derivative_mul_add_mul_eq_one p hp hsep
  let P : StandardEtalePair R := ⟨p, hp, 1, p₁, p₂, 0, by rw [pow_zero, h]⟩
  have hunit : Submonoid.powers (AdjoinRoot.mk P.f P.g) ≤ IsUnit.submonoid (AdjoinRoot P.f) := by
    rintro x ⟨n, rfl⟩
    show IsUnit ((AdjoinRoot.mk P.f P.g) ^ n)
    rw [show P.g = 1 from rfl, map_one, one_pow]
    apply isUnit_one
  let e₁ : AdjoinRoot p ≃ₐ[R] Localization.Away (AdjoinRoot.mk P.f P.g) :=
    (IsLocalization.atUnits (AdjoinRoot P.f) (Submonoid.powers (AdjoinRoot.mk P.f P.g)) hunit).restrictScalars R
  let e : P.Ring ≃ₐ[R] AdjoinRoot p := P.equivAwayAdjoinRoot.trans e₁.symm
  have : Algebra.IsStandardEtale R (AdjoinRoot p) := Algebra.IsStandardEtale.of_equiv e
  infer_instance


private noncomputable def bcHom
  [CommRing R] (S : Type*) [CommRing S] [Algebra R S] (p : R[X]) :
  S ⊗[R] AdjoinRoot p →ₐ[S] AdjoinRoot (p.map (algebraMap R S)) :=
  Algebra.TensorProduct.lift (Algebra.ofId S _)
    (AdjoinRoot.liftAlgHom p (Algebra.ofId R _) (AdjoinRoot.root (p.map (algebraMap R S)))
      (by rw [show ((Algebra.ofId R (AdjoinRoot (p.map (algebraMap R S)))) : R →+* _) = (algebraMap S (AdjoinRoot (p.map (algebraMap R S)))).comp (algebraMap R S) from IsScalarTower.algebraMap_eq R S _, ← eval₂_map, AdjoinRoot.algebraMap_eq, AdjoinRoot.eval₂_root]))
    (fun _ _ => Commute.all _ _)


private noncomputable def bcInv
  [CommRing R] (S : Type*) [CommRing S] [Algebra R S] (p : R[X]) :
  AdjoinRoot (p.map (algebraMap R S)) →ₐ[S] S ⊗[R] AdjoinRoot p :=
  AdjoinRoot.liftAlgHom (p.map (algebraMap R S)) (Algebra.ofId S _) ((1 : S) ⊗ₜ[R] AdjoinRoot.root p)
    (by rw [show ((Algebra.ofId S (S ⊗[R] AdjoinRoot p)) : S →+* _) = algebraMap S (S ⊗[R] AdjoinRoot p) from rfl, eval₂_map, ← IsScalarTower.algebraMap_eq, ← Algebra.TensorProduct.includeRight_apply, ← aeval_def, aeval_algHom_apply, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero])


private lemma bcHom_tmul_one_root
  [CommRing R] (S : Type*) [CommRing S] [Algebra R S] (p : R[X]) :
-- imply
  bcHom S p ((1 : S) ⊗ₜ[R] AdjoinRoot.root p) = AdjoinRoot.root (p.map (algebraMap R S)) := by
-- proof
  simp [bcHom, Algebra.TensorProduct.lift_tmul]


private lemma bcInv_root
  [CommRing R] (S : Type*) [CommRing S] [Algebra R S] (p : R[X]) :
-- imply
  bcInv S p (AdjoinRoot.root (p.map (algebraMap R S))) = (1 : S) ⊗ₜ[R] AdjoinRoot.root p := by
-- proof
  simp [bcInv]


private noncomputable def bcEquiv
  [CommRing R] (S : Type*) [CommRing S] [Algebra R S] (p : R[X]) :
  S ⊗[R] AdjoinRoot p ≃ₐ[S] AdjoinRoot (p.map (algebraMap R S)) := by
  refine AlgEquiv.ofAlgHom (bcHom S p) (bcInv S p) ?_ ?_
  ·
    apply AdjoinRoot.algHom_ext
    rw [AlgHom.comp_apply, bcInv_root, bcHom_tmul_one_root, AlgHom.id_apply]
  ·
    refine Algebra.TensorProduct.ext (by ext) ?_
    apply AdjoinRoot.algHom_ext
    simp [AlgHom.coe_comp, AlgHom.coe_restrictScalars', Function.comp_apply, Algebra.TensorProduct.includeRight_apply]
    rw [bcHom_tmul_one_root, bcInv_root]


/--
[Algebra_Etale_exists_free_nonempty_algEquiv_baseChange_residueField_of_isLocalRing](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_Etale_exists_free_nonempty_algEquiv_baseChange_residueField_of_isLocalRing.lean)
-/
@[path]
private lemma main
  {R : Type u} {Ebar : Type v} [CommRing R] [IsLocalRing R] [CommRing Ebar] [Algebra (IsLocalRing.ResidueField R) Ebar] [Module.Finite (IsLocalRing.ResidueField R) Ebar] [Algebra.Etale (IsLocalRing.ResidueField R) Ebar] :
-- imply
  ∃ (E : Type (max u v)) (_ : CommRing E) (_ : Algebra R E), Module.Finite R E ∧ Module.Free R E ∧ Algebra.Etale R E ∧ Nonempty (IsLocalRing.ResidueField R ⊗[R] E ≃ₐ[IsLocalRing.ResidueField R] Ebar) := by
-- proof
  classical
  let k := IsLocalRing.ResidueField R
  obtain ⟨I, hI, Ai, hF, hAlg, e, hsep⟩ := (Algebra.Etale.iff_exists_algEquiv_prod k Ebar).mp inferInstance
  have := Fintype.ofFinite I
  have : ∀ i, Module.Finite k (Ai i) := fun i => (hsep i).1
  have : ∀ i, Algebra.IsSeparable k (Ai i) := fun i => (hsep i).2
  let pb : ∀ i, PowerBasis k (Ai i) := fun i => Field.powerBasisOfFiniteOfSeparable k (Ai i)
  have hl : ∀ i, ∃ p : R[X], p.map (IsLocalRing.residue R) = minpoly k (pb i).gen ∧ p.Monic := fun i => by
    obtain ⟨p, hp, -, hm⟩ := lifts_and_degree_eq_and_monic
      (map_surjective (IsLocalRing.residue R) IsLocalRing.residue_surjective _)
      (minpoly.monic (pb i).isIntegral_gen)
    refine ⟨p, hp, hm⟩
  choose p hpmap hpmon using hl
  have hpsep : ∀ i, ((p i).map (IsLocalRing.residue R)).Separable := fun i => by
    rw [hpmap]
    apply Algebra.IsSeparable.isSeparable k (pb i).gen
  have : ∀ i, Module.Finite R (AdjoinRoot (p i)) := fun i => (AdjoinRoot.powerBasis' (hpmon i)).finite
  have : ∀ i, Module.Free R (AdjoinRoot (p i)) := fun i =>
    Module.Free.of_basis (R := R) (M := AdjoinRoot (p i)) (AdjoinRoot.powerBasis' (hpmon i)).basis
  have : ∀ i, Algebra.Etale R (AdjoinRoot (p i)) := fun i => etale_adjoinRoot (p i) (hpmon i) (hpsep i)
  refine ⟨(i : I) → AdjoinRoot (p i), inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ⟨?_⟩⟩
  have hq : ∀ i, (p i).map (algebraMap R k) = minpoly k (pb i).gen := fun i => by
    rw [IsLocalRing.ResidueField.algebraMap_eq]
    apply hpmap i
  let f : ∀ i, AdjoinRoot ((p i).map (algebraMap R k)) ≃ₐ[k] Ai i := fun i =>
    (AdjoinRoot.algEquivOfEq k _ _ (hq i)).trans
      ((AdjoinRoot.powerBasis (minpoly.ne_zero (pb i).isIntegral_gen)).equivOfMinpoly (pb i)
        (AdjoinRoot.minpoly_powerBasis_gen_of_monic (minpoly.monic (pb i).isIntegral_gen)))
  apply ((Algebra.TensorProduct.piRight R k k (fun i => AdjoinRoot (p i))).trans
    (AlgEquiv.piCongrRight fun i => (bcEquiv k (p i)).trans (f i))).trans e.symm


-- created on 2026-10-13
