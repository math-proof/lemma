module

public import Mathlib
public import Theorem.Rep.SUnitsModule
public import Instance.ExtEndgame_ProductionDatum
public import Theorem.ClassGroup.GaloisAction
public import Theorem.Ideal.Mathlib430
public import Instance.NumberField_LevelArithmeticModP
public import Abbrev.NumberField_LevelArithmeticModP

public noncomputable section

set_option autoImplicit false

noncomputable section

open CategoryTheory IsDedekindDomain
open scoped Pointwise NumberField nonZeroDivisors Rep

namespace NumberField.LevelArith

section Bridge

variable (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hKL : K ≤ L)


@[simp] public theorem coe_levelFieldEquiv (x : ↥L) : ((levelFieldEquiv K L hKL x : ↥(levelField K L hKL)) : AlgebraicClosure ℚ) = x := rfl


@[simp] public theorem coe_levelFieldEquiv_symm (y : ↥(levelField K L hKL)) :
    (((levelFieldEquiv K L hKL).symm y : ↥L) : AlgebraicClosure ℚ) = y := rfl


public theorem levelGal_apply_coe [Normal ↥K ↥(levelField K L hKL)] (γ : ↥K.fixingSubgroup) (x : ↥(levelField K L hKL)) :
    ((levelGal K L hKL γ x : ↥(levelField K L hKL)) : AlgebraicClosure ℚ) =
      (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : AlgebraicClosure ℚ) :=
  AlgEquiv.restrictNormal_commutes (IntermediateField.fixingSubgroupEquiv K γ) ↥(levelField K L hKL) x


public theorem levelGal_eq_one_of_mem [Normal ↥K ↥(levelField K L hKL)] (γ : ↥K.fixingSubgroup)
    (hγ : (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ L.fixingSubgroup) : levelGal K L hKL γ = 1 :=
  AlgEquiv.ext fun x => Subtype.ext (by
    rw [levelGal_apply_coe]
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hγ _ ((IntermediateField.mem_extendScalars hKL).1 x.2))


public theorem inflLevel_ρ_apply [Normal ↥K ↥(levelField K L hKL)] {k : Type} [CommRing k] (M : Rep k (LevelGal K L hKL))
    (γ : ↥K.fixingSubgroup) : (inflLevel K L hKL M).ρ γ = M.ρ (levelGal K L hKL γ) := rfl

end Bridge

section ModP

variable {k : Type} [CommRing k] {G : Type} [Group G]


public theorem torsionBy_le_comap {M : Type} [AddCommGroup M] {iM : Module k M} (ρ : Representation k G M) (a : k)
    (g : G) : Submodule.torsionBy k M a ≤ (Submodule.torsionBy k M a).comap (ρ g) := fun x hx => by
  rw [Submodule.mem_comap, Submodule.mem_torsionBy_iff, ← map_smul]
  rw [Submodule.mem_torsionBy_iff] at hx
  rw [hx, map_zero]


public theorem smul_top_le_comap {M : Type} [AddCommGroup M] {iM : Module k M} (ρ : Representation k G M) (a : k)
    (g : G) : (a • (⊤ : Submodule k M)) ≤ (a • (⊤ : Submodule k M)).comap (ρ g) := fun x hx => by
  rw [Submodule.mem_comap]
  obtain ⟨y, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
  rw [map_smul]
  exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top


public theorem nsmul_quot_eq_zero {V : Type} [AddCommGroup V] {iV : Module k V} (p : ℕ) (x : V ⧸ ((p : k) • (⊤ : Submodule k V))) :
    p • x = 0 := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.mkQ_apply, ← map_nsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, ← Nat.cast_smul_eq_nsmul k]
  exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top


public theorem nsmul_torsionBy_eq_zero {V : Type} [AddCommGroup V] {iV : Module k V} (p : ℕ) (x : ↥(Submodule.torsionBy k V (p : k))) :
    p • x = 0 := by
  rw [← Nat.cast_smul_eq_nsmul k]
  exact Subtype.ext ((Submodule.mem_torsionBy_iff (p : k) (x : V)).1 x.2)


@[simp] public theorem toZMod_apply (p : ℕ) {M : Type} [AddCommGroup M] [Module (ZMod p) M] {inst : Module k M}
    (σ : Representation k G M) (g : G) (m : M) : toZMod p σ g m = σ g m := rfl


@[simp] public theorem modP_apply_mk (p : ℕ) {V : Type} [AddCommGroup V] {iV : Module k V} (ρ : Representation k G V) (g : G) (v : V) :
    modP p ρ g (Submodule.Quotient.mk v) = Submodule.Quotient.mk (ρ g v) := rfl


@[simp] public theorem torsionP_apply_coe (p : ℕ) {V : Type} [AddCommGroup V] {iV : Module k V} (ρ : Representation k G V) (g : G)
    (v : ↥(Submodule.torsionBy k V (p : k))) : ((torsionP p ρ g v : ↥(Submodule.torsionBy k V (p : k))) : V) = ρ g v := rfl


@[simp] public theorem repModPMap_hom_mk (p : ℕ) {A B : Rep k G} (f : A ⟶ B) (a : A) :
    (repModPMap p f).hom (Submodule.Quotient.mk a) = Submodule.Quotient.mk (f.hom a) := rfl


@[simp] public theorem repTorsionPMap_hom_apply_coe (p : ℕ) {A B : Rep k G} (f : A ⟶ B) (a : ↥(Submodule.torsionBy k A (p : k))) :
    (((repTorsionPMap p f).hom a : ↥(Submodule.torsionBy k B (p : k))) : B) = f.hom a := rfl

end ModP

section ClassGroups

variable (E F : Type) [Field E] [Field F] [NumberField F] [Algebra E F]


public theorem smul_classGroup_def (σ : F ≃ₐ[E] F) (C : ClassGroup (𝓞 F)) : σ • C = ClassGroup.mulEquiv (ringOfIntegersAut E F σ) C := rfl


public theorem smul_mk0 (σ : F ≃ₐ[E] F) (P : (Ideal (𝓞 F))⁰) : σ • ClassGroup.mk0 P = ClassGroup.mk0 (Ideal.mapNonZero (ringOfIntegersAut E F σ) P) :=
  ClassGroup.mulEquiv_mk0 _ P


public theorem mem_placesOverPrimes_iff (S : Set Nat.Primes) (w : HeightOneSpectrum (𝓞 F)) :
    w ∈ placesOverPrimes F S ↔ ∃ p ∈ S, ((p : ℕ) : 𝓞 F) ∈ w.asIdeal := Iff.rfl


public theorem placesOverPrimes_finite (S : Finset Nat.Primes) : (placesOverPrimes F (S : Set Nat.Primes)).Finite := by
  refine (S.finite_toSet.biUnion fun p _ => (Ideal.finite_factors (I := Ideal.span {((p : ℕ) : 𝓞 F)}) ?_)).subset ?_
  · rw [Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast p.2.ne_zero
  · rintro w ⟨p, hp, hw⟩
    exact Set.mem_biUnion hp ((Ideal.dvd_iff_le).2 ((Ideal.span_singleton_le_iff_mem _).2 hw))


public theorem mem_placesOverPrimesFinset (S : Finset Nat.Primes) (w : HeightOneSpectrum (𝓞 F)) :
    w ∈ placesOverPrimesFinset F S ↔ w ∈ placesOverPrimes F (S : Set Nat.Primes) := Set.Finite.mem_toFinset _


public theorem mem_sPrimeClasses_iff (S : Set Nat.Primes) (c : ClassGroup (𝓞 F)) :
    c ∈ sPrimeClasses E F S ↔ ∀ σ : F ≃ₐ[E] F, σ • c ∈ Subgroup.closure (primeClass F '' placesOverPrimes F S) := by
  simp only [sPrimeClasses, Subgroup.mem_iInf, Subgroup.mem_comap, MulDistribMulAction.toMonoidHom_apply]


public theorem smul_mem_sPrimeClasses (S : Set Nat.Primes) (τ : F ≃ₐ[E] F) {c : ClassGroup (𝓞 F)} (hc : c ∈ sPrimeClasses E F S) :
    τ • c ∈ sPrimeClasses E F S := by
  rw [mem_sPrimeClasses_iff] at hc ⊢
  intro σ
  rw [← mul_smul]
  exact hc (σ * τ)


public theorem mem_sPrimeClassesSubmodule (S : Set Nat.Primes) (x : Additive (ClassGroup (𝓞 F))) :
    x ∈ sPrimeClassesSubmodule E F S ↔ Additive.toMul x ∈ sPrimeClasses E F S := Iff.rfl


public theorem toSClassGroupRep_hom_apply (S : Set Nat.Primes) (x : classGroupRep E F) :
    (toSClassGroupRep E F S).hom x = Submodule.Quotient.mk x := rfl


public theorem toSClassGroupRep_hom_surjective (S : Set Nat.Primes) : Function.Surjective (toSClassGroupRep E F S).hom :=
  Submodule.mkQ_surjective _

end ClassGroups

section Quartet

variable (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hKL : K ≤ L) [Normal ↥K ↥(levelField K L hKL)]
  [FiniteDimensional ℚ ↥K] [FiniteDimensional ℚ ↥L] (S : Finset Nat.Primes) (p : ℕ)


public theorem orbitQuotientAction_smul_mk (hnorm : IsNormalLevel K L) (X : Type) [MulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) X] (γ : ↥K.fixingSubgroup) (x : X) :
    (letI := orbitQuotientAction K L hnorm X
     γ • (Quotient.mk'' x : MulAction.orbitRel.Quotient ↥L.fixingSubgroup X)) = Quotient.mk'' ((γ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) • x) := rfl


public theorem orbitQuotientAction_smul_eq_of_mem (hnorm : IsNormalLevel K L) (X : Type) [MulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) X] (γ : ↥K.fixingSubgroup)
    (hγ : (γ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) ∈ L.fixingSubgroup) (q : MulAction.orbitRel.Quotient ↥L.fixingSubgroup X) :
    (letI := orbitQuotientAction K L hnorm X; γ • q) = q := by
  induction q using Quotient.inductionOn' with
  | h x => exact Quotient.sound' ((MulAction.orbitRel_apply).2 (MulAction.mem_orbit_iff.2 ⟨⟨_, hγ⟩, rfl⟩))


public theorem placesRep_ρ_single (hnorm : IsNormalLevel K L) (S : Finset Nat.Primes) (v : ExtCitation.extArithIndex S) (p : ℕ)
    (γ : ↥K.fixingSubgroup) (x : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ (ExtCitation.extArithLoc S v).range) (c : ZMod p) :
    (placesRep K L hnorm S v p).ρ γ (Finsupp.single (Quotient.mk'' x) c) = Finsupp.single (Quotient.mk'' ((γ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) • x)) c :=
  Finsupp.mapDomain_single


public theorem placesAug_hom_single (hnorm : IsNormalLevel K L) (S : Finset Nat.Primes) (v : ExtCitation.extArithIndex S) (p : ℕ)
    (q : placesAbove L (ExtCitation.extArithLoc S v).range) (c : ZMod p) : (placesAug K L hnorm S v p).hom (Finsupp.single q c) = c := by
  change Finsupp.linearCombination (ZMod p) (fun _ => (1 : ZMod p)) (Finsupp.single q c) = c
  rw [Finsupp.linearCombination_single, smul_eq_mul, mul_one]

end Places

end NumberField.LevelArith

end
