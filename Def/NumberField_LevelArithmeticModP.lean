module
public import Mathlib
public import Def.NumberField_SUnitsModule
public import Instance.ExtEndgame_ProductionDatum
public import Def.ClassGroup_GaloisAction
public import Def.Ideal_Mathlib430
public import Instance.NumberField_LevelArithmeticModP
public import Abbrev.NumberField_LevelArithmeticModP
set_option autoImplicit false


public section

noncomputable section

open CategoryTheory IsDedekindDomain
open scoped Pointwise NumberField nonZeroDivisors Rep

namespace NumberField.LevelArith

section Bridge

variable (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hKL : K ≤ L)

def levelFieldEquiv : ↥L ≃+* ↥(levelField K L hKL) where
  toFun x := ⟨(x : AlgebraicClosure ℚ), (IntermediateField.mem_extendScalars hKL).2 x.2⟩
  invFun y := ⟨(y : AlgebraicClosure ℚ), (IntermediateField.mem_extendScalars hKL).1 y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

def levelGal [Normal ↥K ↥(levelField K L hKL)] : ↥K.fixingSubgroup →* LevelGal K L hKL :=
  (AlgEquiv.restrictNormalHom ↥(levelField K L hKL)).comp (IntermediateField.fixingSubgroupEquiv K).toMonoidHom

abbrev inflLevel [Normal ↥K ↥(levelField K L hKL)] {k : Type} [CommRing k] (M : Rep k (LevelGal K L hKL)) : Rep k ↥K.fixingSubgroup :=
  Rep.res (levelGal K L hKL) M

end Bridge

section ModP

variable {k : Type} [CommRing k] {G : Type} [Group G]

def toZMod (p : ℕ) {M : Type} [AddCommGroup M] [Module (ZMod p) M] {inst : Module k M} (σ : Representation k G M) :
    Representation (ZMod p) G M where
  toFun g := (σ g).toAddMonoidHom.toZModLinearMap p
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

def modP (p : ℕ) {V : Type} [AddCommGroup V] {iV : Module k V} (ρ : Representation k G V) :
    Representation (ZMod p) G (V ⧸ ((p : k) • (⊤ : Submodule k V))) :=
  toZMod p (ρ.quotient _ (smul_top_le_comap ρ (p : k)))

def torsionP (p : ℕ) {V : Type} [AddCommGroup V] {iV : Module k V} (ρ : Representation k G V) :
    Representation (ZMod p) G ↥(Submodule.torsionBy k V (p : k)) :=
  toZMod p (ρ.subrepresentation _ (torsionBy_le_comap ρ (p : k)))

abbrev repModP (p : ℕ) (A : Rep k G) : Rep (ZMod p) G := Rep.of (modP p A.ρ)

abbrev repTorsionP (p : ℕ) (A : Rep k G) : Rep (ZMod p) G := Rep.of (torsionP p A.ρ)

def repModPMap (p : ℕ) {A B : Rep k G} (f : A ⟶ B) : repModP p A ⟶ repModP p B :=
  Rep.ofHom ⟨(Submodule.mapQ ((p : k) • (⊤ : Submodule k A)) ((p : k) • (⊤ : Submodule k B)) f.hom.toLinearMap (fun x hx => by
      obtain ⟨y, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
      rw [Submodule.mem_comap, map_smul]
      exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top)).toAddMonoidHom.toZModLinearMap p,
    fun g => LinearMap.ext fun x => by
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      change Submodule.Quotient.mk (f.hom (A.ρ g a)) = Submodule.Quotient.mk (B.ρ g (f.hom a))
      rw [Rep.hom_comm_apply]⟩

def repTorsionPMap (p : ℕ) {A B : Rep k G} (f : A ⟶ B) : repTorsionP p A ⟶ repTorsionP p B :=
  Rep.ofHom ⟨(f.hom.toLinearMap.restrict (p := Submodule.torsionBy k A (p : k)) (q := Submodule.torsionBy k B (p : k)) (fun x hx => by
      rw [Submodule.mem_torsionBy_iff] at hx ⊢
      rw [← map_smul, hx, map_zero])).toAddMonoidHom.toZModLinearMap p,
    fun g => LinearMap.ext fun x => Subtype.ext (Rep.hom_comm_apply f g (x : A))⟩

end ModP

section ClassGroups

variable (E F : Type) [Field E] [Field F] [NumberField F] [Algebra E F]

def classGroupAut : (F ≃ₐ[E] F) →* MulAut (ClassGroup (𝓞 F)) where
  toFun σ := ClassGroup.mulEquiv (ringOfIntegersAut E F σ)
  map_one' := MulEquiv.ext fun C => by
    change ClassGroup.mulEquiv (ringOfIntegersAut E F 1) C = C
    have : ringOfIntegersAut E F 1 = RingEquiv.refl _ := RingEquiv.ext fun _ => rfl
    rw [this, ClassGroup.mulEquiv_refl_apply]
  map_mul' σ τ := MulEquiv.ext fun C => by
    change ClassGroup.mulEquiv (ringOfIntegersAut E F (σ * τ)) C =
      ClassGroup.mulEquiv (ringOfIntegersAut E F σ) (ClassGroup.mulEquiv (ringOfIntegersAut E F τ) C)
    have : ringOfIntegersAut E F (σ * τ) = (ringOfIntegersAut E F τ).trans (ringOfIntegersAut E F σ) := RingEquiv.ext fun _ => rfl
    rw [this, ClassGroup.mulEquiv_trans_apply]

def placesOverPrimes (S : Set Nat.Primes) : Set (HeightOneSpectrum (𝓞 F)) := {w | ∃ p ∈ S, ((p : ℕ) : 𝓞 F) ∈ w.asIdeal}

omit [NumberField F] in
def placesOverPrimesFinset (S : Finset Nat.Primes) : Finset (HeightOneSpectrum (𝓞 F)) := (placesOverPrimes_finite F S).toFinset

def primeClass (w : HeightOneSpectrum (𝓞 F)) : ClassGroup (𝓞 F) :=
  ClassGroup.mk0 ⟨w.asIdeal, mem_nonZeroDivisors_iff_ne_zero.2 (by simpa using w.ne_bot)⟩

def sPrimeClasses (S : Set Nat.Primes) : Subgroup (ClassGroup (𝓞 F)) :=
  ⨅ σ : F ≃ₐ[E] F, (Subgroup.closure (primeClass F '' placesOverPrimes F S)).comap (MulDistribMulAction.toMonoidHom (ClassGroup (𝓞 F)) σ)

def sPrimeClassesSubmodule (S : Set Nat.Primes) : Submodule ℤ (Additive (ClassGroup (𝓞 F))) :=
  (Subgroup.toAddSubgroup (sPrimeClasses E F S)).toIntSubmodule

abbrev sClassGroupRep (S : Set Nat.Primes) : Rep ℤ (F ≃ₐ[E] F) :=
  Rep.of (X := (Additive (ClassGroup (𝓞 F))) ⧸ sPrimeClassesSubmodule E F S)
    ((Representation.ofMulDistribMulAction (F ≃ₐ[E] F) (ClassGroup (𝓞 F))).quotient
      (sPrimeClassesSubmodule E F S) fun σ x hx => by
        have hx' : Additive.toMul x ∈ sPrimeClasses E F S := (mem_sPrimeClassesSubmodule E F S x).1 hx
        have hρ := Representation.ofMulDistribMulAction_apply_apply
          (M := F ≃ₐ[E] F) (G := ClassGroup (𝓞 F)) σ x
        have : Additive.toMul
            (Representation.ofMulDistribMulAction (F ≃ₐ[E] F) (ClassGroup (𝓞 F)) σ x)
            ∈ sPrimeClasses E F S := by
          rw [hρ, toMul_ofMul]
          exact smul_mem_sPrimeClasses E F S σ hx'
        exact (mem_sPrimeClassesSubmodule E F S _).2 this)

def toSClassGroupRep (S : Set Nat.Primes) : classGroupRep E F ⟶ sClassGroupRep E F S :=
  Rep.ofHom ⟨Submodule.mkQ _, fun _ => rfl⟩

end ClassGroups

section Quartet

variable (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hKL : K ≤ L) [Normal ↥K ↥(levelField K L hKL)]
  [FiniteDimensional ℚ ↥K] [FiniteDimensional ℚ ↥L] (S : Finset Nat.Primes) (p : ℕ)

abbrev unitsModP : Rep (ZMod p) ↥K.fixingSubgroup :=
  inflLevel K L hKL (repModP p (NumberField.SUnits.sUnitsRep ↥K ↥(levelField K L hKL) (placesOverPrimesFinset ↥K S)))

abbrev sClassTorsionP : Rep (ZMod p) ↥K.fixingSubgroup :=
  inflLevel K L hKL (repTorsionP p (sClassGroupRep ↥K ↥(levelField K L hKL) (S : Set Nat.Primes)))

abbrev sClassModP : Rep (ZMod p) ↥K.fixingSubgroup :=
  inflLevel K L hKL (repModP p (sClassGroupRep ↥K ↥(levelField K L hKL) (S : Set Nat.Primes)))

end Quartet

section Places

variable (K L : IntermediateField ℚ (AlgebraicClosure ℚ))

@[reducible] def orbitQuotientAction (hnorm : IsNormalLevel K L) (X : Type) [MulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) X] :
    MulAction ↥K.fixingSubgroup (MulAction.orbitRel.Quotient ↥L.fixingSubgroup X) where
  smul γ := Quotient.map' (fun x : X => (γ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) • x) (fun a b hab => by
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hab ⊢
    obtain ⟨s, rfl⟩ := hab
    refine ⟨⟨(γ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) * s * (γ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))⁻¹, hnorm _ γ.2 _ s.2⟩, ?_⟩
    show ((γ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) * s * (γ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))⁻¹) • ((γ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) • b) = (γ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) • ((s : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) • b)
    rw [← mul_smul, ← mul_smul, inv_mul_cancel_right])
  one_smul q := Quotient.inductionOn' q fun x => congrArg (Quotient.mk'' (s₁ := MulAction.orbitRel ↥L.fixingSubgroup X))
    (one_smul (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) x)
  mul_smul γ δ q := Quotient.inductionOn' q fun x => congrArg (Quotient.mk'' (s₁ := MulAction.orbitRel ↥L.fixingSubgroup X))
    (mul_smul (γ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (δ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) x)

def placesRep (hnorm : IsNormalLevel K L) (S : Finset Nat.Primes) (v : ExtCitation.extArithIndex S) (p : ℕ) :
    Rep (ZMod p) ↥K.fixingSubgroup :=
  Rep.of (@Representation.ofMulActionFinsupp (ZMod p) _ ↥K.fixingSubgroup _ (placesAbove L (ExtCitation.extArithLoc S v).range) (orbitQuotientAction K L hnorm _))

def placesAug (hnorm : IsNormalLevel K L) (S : Finset Nat.Primes) (v : ExtCitation.extArithIndex S) (p : ℕ) :
    placesRep K L hnorm S v p ⟶ Rep.trivial (ZMod p) ↥K.fixingSubgroup (ZMod p) :=
  Rep.ofHom ⟨Finsupp.linearCombination (ZMod p) (fun _ => (1 : ZMod p)), fun γ => Finsupp.lhom_ext fun q c => by
    change Finsupp.linearCombination (ZMod p) (fun _ => (1 : ZMod p)) (Finsupp.mapDomain _ (Finsupp.single q c)) =
      Finsupp.linearCombination (ZMod p) (fun _ => (1 : ZMod p)) (Finsupp.single q c)
    rw [Finsupp.mapDomain_single, Finsupp.linearCombination_single, Finsupp.linearCombination_single]⟩

end Places

end NumberField.LevelArith

end
