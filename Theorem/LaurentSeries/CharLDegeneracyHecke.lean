module

public import Theorem.Scheme.CharLSpecialFibrePic0CommutingFamilyBridge

public noncomputable section

set_option autoImplicit false

noncomputable section

open AlgebraicCurve

namespace AlgebraicCurve

namespace Divisor

variable {K F : Type*} [Field K] [Field F] [Algebra K F]


@[simp]
public theorem coe_degZeroEnd (T : Divisor K F →+ Divisor K F) (h : DescendsToPic0 T)
    (D : Divisor.degZero (K := K) (F := F)) : (degZeroEnd T h D : Divisor K F) = T D :=
  rfl

open Classical in


public theorem toPic0End_eq (T : Divisor K F →+ Divisor K F) (h : DescendsToPic0 T) :
    toPic0End T = QuotientAddGroup.map _ _ (degZeroEnd T h) (by
      rintro ⟨D, hD0⟩ hD
      simp only [AddSubgroup.mem_addSubgroupOf] at hD ⊢
      exact h.2 D hD) := by
  rw [toPic0End, dif_pos h]


public theorem toPic0End_mk (T : Divisor K F →+ Divisor K F) (h : DescendsToPic0 T)
    (D : Divisor.degZero (K := K) (F := F)) :
    toPic0End T (Pic0.mk D) = Pic0.mk (degZeroEnd T h D) := by
  rw [toPic0End_eq T h]
  rfl


public theorem toPic0End_of_not (T : Divisor K F →+ Divisor K F) (h : ¬ DescendsToPic0 T) : toPic0End T = 0 := by
  rw [toPic0End, dif_neg h]

end Divisor

end AlgebraicCurve

namespace ModularCurve

section CharSlot

variable (K : Type*) [Field K] (N : ℕ) [NeZero N] {ℓ : ℕ} [hℓ : Fact ℓ.Prime] [CharP K ℓ]
variable (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)


public theorem heckePic0FibreChar_apply (x : Pic0 K (modularFunctionFieldC K N)) :
    heckePic0FibreChar K N data hKr x = Divisor.toPic0End (heckeFibreGeomLevel K N data hKr) x :=
  rfl


public theorem heckeFibreGeomLevel_indep (data' : ModularPolynomialData ℓ) (hKr' : KroneckerCongruence ℓ data') :
    heckeFibreGeomLevel K N data hKr = heckeFibreGeomLevel K N data' hKr' :=
  rfl


public theorem heckePic0FibreChar_indep (data' : ModularPolynomialData ℓ) (hKr' : KroneckerCongruence ℓ data') :
    heckePic0FibreChar K N data hKr = heckePic0FibreChar K N data' hKr' :=
  rfl


public theorem descendsToPic0_heckeFibreGeomLevel (hperf : ∀ c : K, ∃ d : K, d ^ ℓ = c)
    (hdeg1 : ∀ w : Place K (modularFunctionFieldC K N), w.deg = 1) :
    Divisor.DescendsToPic0 (heckeFibreGeomLevel K N data hKr) :=
  ⟨fun _ hD => heckeFibreGeomLevel_mem_degZero K N data hKr hdeg1 hD,
    fun _ hD => isPrincipal_heckeFibreGeomLevel' K N data hKr hperf
      (frobOnPlacesGeomLevel_surjective K N data hKr hperf) hD⟩


public theorem heckePic0FibreChar_eq_heckeFibreGeomLevelPic0OfIsCurveOver [IsAlgClosed K]
    [IsCurveOver K (modularFunctionFieldC K N)] :
    heckePic0FibreChar K N data hKr = (heckeFibreGeomLevelPic0OfIsCurveOver K N data hKr).toIntLinearMap := by
  have h := descendsToPic0_heckeFibreGeomLevel K N data hKr (perfect_of_isAlgClosed K)
    (deg_eq_one_modularFunctionFieldC K N)
  refine LinearMap.ext fun x => ?_
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  rw [heckePic0FibreChar_apply, Divisor.toPic0End_mk _ h, AddMonoidHom.coe_toIntLinearMap,
    heckeFibreGeomLevelPic0OfIsCurveOver_eq, heckeFibreGeomLevelPic0_mk]
  exact congrArg Pic0.mk (Subtype.ext rfl)

end CharSlot

section Family

variable (K : Type*) [Field K] (N : ℕ) [NeZero N] {ℓ : ℕ} [hℓ : Fact ℓ.Prime] [CharP K ℓ]
variable (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)
variable (Tne : Nat.Primes → Module.End ℤ (Pic0 K (modularFunctionFieldC K N)))


public theorem heckeFamilyFibreOf_of_eq {q : Nat.Primes} (hq : (q : ℕ) = ℓ) :
    heckeFamilyFibreOf K N data hKr Tne q = heckePic0FibreChar K N data hKr :=
  if_pos hq


public theorem heckeFamilyFibreOf_of_ne {q : Nat.Primes} (hq : (q : ℕ) ≠ ℓ) :
    heckeFamilyFibreOf K N data hKr Tne q = Tne q :=
  if_neg hq


public theorem heckeModuleFibreOf_smul_def (h : HeckeOperatorsCommuteFibreOf K N data hKr Tne) (t : HeckeAlg)
    (x : Pic0 K (modularFunctionFieldC K N)) :
    (letI := heckeModuleFibreOf K N data hKr Tne; t • x) = (heckeCommutingFamilyFibreOf h).endHom t x := by
  have e : heckeModuleFibreOf K N data hKr Tne = (heckeCommutingFamilyFibreOf h).module := dif_pos h
  rw [e]
  rfl


public theorem heckeModuleFibreOf_heckeGen_smul (h : HeckeOperatorsCommuteFibreOf K N data hKr Tne) (q : Nat.Primes)
    (x : Pic0 K (modularFunctionFieldC K N)) :
    (letI := heckeModuleFibreOf K N data hKr Tne; heckeGen q • x) = heckeFamilyFibreOf K N data hKr Tne q x := by
  rw [heckeModuleFibreOf_smul_def h, CommutingHeckeFamily.endHom_heckeGen]
  rfl


public theorem heckeModuleFibreOf_heckeGen_smul_char (h : HeckeOperatorsCommuteFibreOf K N data hKr Tne) {q : Nat.Primes}
    (hq : (q : ℕ) = ℓ) (x : Pic0 K (modularFunctionFieldC K N)) :
    (letI := heckeModuleFibreOf K N data hKr Tne; heckeGen q • x) = heckePic0FibreChar K N data hKr x := by
  rw [heckeModuleFibreOf_heckeGen_smul h, heckeFamilyFibreOf_of_eq K N data hKr Tne hq]


public theorem heckeModuleFibreOf_heckeGen_smul_of_ne (h : HeckeOperatorsCommuteFibreOf K N data hKr Tne) {q : Nat.Primes}
    (hq : (q : ℕ) ≠ ℓ) (x : Pic0 K (modularFunctionFieldC K N)) :
    (letI := heckeModuleFibreOf K N data hKr Tne; heckeGen q • x) = Tne q x := by
  rw [heckeModuleFibreOf_heckeGen_smul h, heckeFamilyFibreOf_of_ne K N data hKr Tne hq]


public theorem heckeModuleFibreOf_smul_of_not (h : ¬ HeckeOperatorsCommuteFibreOf K N data hKr Tne) (t : HeckeAlg)
    (x : Pic0 K (modularFunctionFieldC K N)) :
    (letI := heckeModuleFibreOf K N data hKr Tne; t • x) = MvPolynomial.constantCoeff t • x := by
  have e : heckeModuleFibreOf K N data hKr Tne =
      Module.compHom (Pic0 K (modularFunctionFieldC K N))
        (MvPolynomial.eval₂Hom (Int.castRingHom ℤ) (0 : Nat.Primes → ℤ)) :=
    dif_neg h
  rw [e]
  show (MvPolynomial.eval₂Hom (Int.castRingHom ℤ) (0 : Nat.Primes → ℤ) t) • x = _
  rw [MvPolynomial.eval₂Hom_zero_apply, eq_intCast, Int.cast_id]


public theorem heckeModuleFibreOf_heckeGen_smul_of_not (h : ¬ HeckeOperatorsCommuteFibreOf K N data hKr Tne)
    (q : Nat.Primes) (x : Pic0 K (modularFunctionFieldC K N)) :
    (letI := heckeModuleFibreOf K N data hKr Tne; heckeGen q • x) = 0 := by
  rw [heckeModuleFibreOf_smul_of_not h, heckeGen, MvPolynomial.constantCoeff_X, zero_zsmul]


public theorem endHom_C' {J' : Type*} [AddCommGroup J'] (fam : CommutingHeckeFamily J') (a : ℤ) :
    fam.endHom (MvPolynomial.C a) = (a : Module.End ℤ J') := by
  rw [← MvPolynomial.algebraMap_eq, eq_intCast, map_intCast]


public theorem heckeModuleFibreOf_C_smul (a : ℤ) (x : Pic0 K (modularFunctionFieldC K N)) :
    (letI := heckeModuleFibreOf K N data hKr Tne; (MvPolynomial.C a : HeckeAlg) • x) = a • x := by
  by_cases h : HeckeOperatorsCommuteFibreOf K N data hKr Tne
  · rw [heckeModuleFibreOf_smul_def h, endHom_C', Module.End.intCast_apply]
  · rw [heckeModuleFibreOf_smul_of_not h, MvPolynomial.constantCoeff_C]

end Family

section Match

variable (K : Type*) [Field K] (N : ℕ) [NeZero N] [IsAlgClosed K] [IsCurveOver K (modularFunctionFieldC K N)]
variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] [CharP K ℓ]
variable (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)
variable (Tne : Nat.Primes → Module.End ℤ (Pic0 K (modularFunctionFieldC K N)))


public theorem pic0SpecialFibreCommutingFamilyMatch_heckeCommutingFamilyFibreOf
    (h : HeckeOperatorsCommuteFibreOf K N data hKr Tne) :
    Pic0SpecialFibreCommutingFamilyMatch K N data hKr (heckeCommutingFamilyFibreOf h) := by
  show heckeFamilyFibreOf K N data hKr Tne ⟨ℓ, hℓ.out⟩ = _
  rw [heckeFamilyFibreOf_of_eq K N data hKr Tne rfl,
    heckePic0FibreChar_eq_heckeFibreGeomLevelPic0OfIsCurveOver K N data hKr]


public theorem specialFibreHeckeModuleMatch_heckeModuleFibreOf (h : HeckeOperatorsCommuteFibreOf K N data hKr Tne) :
    SpecialFibreHeckeModuleMatch K N data hKr (heckeModuleFibreOf K N data hKr Tne) := by
  have e : heckeModuleFibreOf K N data hKr Tne = (heckeCommutingFamilyFibreOf h).module := dif_pos h
  rw [e]
  exact specialFibreHeckeModuleMatch_of_commutingFamily K N data hKr _
    (pic0SpecialFibreCommutingFamilyMatch_heckeCommutingFamilyFibreOf K N data hKr Tne h)

end Match

end ModularCurve

namespace ModularCurve

variable (k : Type*) [Field k] (N q : ℕ) [NeZero N] [NeZero q]


public theorem modularFunctionFieldC_le_charLDegeneracyRoof :
    modularFunctionFieldC k N ≤ charLDegeneracyRoof k N q := by
  unfold modularFunctionFieldC charLDegeneracyRoof
  apply IntermediateField.adjoin.mono
  intro x hx
  rcases hx with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)


public theorem qExpand_image_le_charLDegeneracyRoof :
    (modularFunctionFieldC k N).map (qExpandAlgC k q) ≤ charLDegeneracyRoof k N q := by
  unfold modularFunctionFieldC
  rw [IntermediateField.adjoin_map]
  apply IntermediateField.adjoin.mono
  rintro x hx
  simp only [Set.image_insert_eq, Set.image_singleton, qExpandAlgC_apply] at hx
  rcases hx with h | h
  · subst h
    exact Or.inr (Or.inr (Or.inl rfl))
  · rw [Set.mem_singleton_iff] at h
    subst h
    refine Or.inr (Or.inr (Or.inr ?_))
    rw [Set.mem_singleton_iff]
    show qExpand k q (jqNModC k N) = jqNModC k (N * q)
    unfold jqNModC
    rw [qExpand_qExpand]
    simp only [Nat.mul_comm q N]


@[simp]
public theorem coe_heckeAlphaC (x : modularFunctionFieldC k N) :
    (heckeAlphaC k N q x : LaurentSeries k) = (x : LaurentSeries k) :=
  IntermediateField.coe_inclusion _ x


@[simp]
public theorem coe_heckeBetaC (x : modularFunctionFieldC k N) :
    (heckeBetaC k N q x : LaurentSeries k) = qExpand k q (x : LaurentSeries k) :=
  rfl


public theorem heckeInputsFibre_intro
    [hP : HasPrincipalDivisors k (charLDegeneracyRoof k N q)]
    (hβ : HeckeBetaCIntegral k N q) (hα : HeckeAlphaCIntegral k N q)
    (hdesc : AlgebraicCurve.Divisor.DescendsToPic0 (heckeDivFibre k N q hβ hα)) :
    HeckeInputsFibre k N q :=
  ⟨hP, hβ, hα, hdesc⟩


public theorem heckePic0Fibre_eq
    [hP : HasPrincipalDivisors k (charLDegeneracyRoof k N q)]
    (hβ : HeckeBetaCIntegral k N q) (hα : HeckeAlphaCIntegral k N q)
    (hdesc : AlgebraicCurve.Divisor.DescendsToPic0 (heckeDivFibre k N q hβ hα)) :
    heckePic0Fibre k N q
      = (AlgebraicCurve.Divisor.toPic0End (heckeDivFibre k N q hβ hα)).toIntLinearMap := by
  rw [heckePic0Fibre, dif_pos (heckeInputsFibre_intro k N q hβ hα hdesc)]


public theorem heckePic0Fibre_of_not (h : ¬ HeckeInputsFibre k N q) : heckePic0Fibre k N q = 0 := by
  rw [heckePic0Fibre, dif_neg h]

section Instantiated

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] [CharP k ℓ]
  (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)


public theorem heckeModuleFibre_heckeGen_smul (h : HeckeOperatorsCommuteFibre k N data hKr)
    (q' : Nat.Primes) (x : Pic0 k (modularFunctionFieldC k N)) :
    (letI := heckeModuleFibre k N data hKr; heckeGen q' • x)
      = heckeFamilyFibre k N data hKr q' x :=
  heckeModuleFibreOf_heckeGen_smul (K := k) (N := N) (data := data) (hKr := hKr)
    (Tne := fun p' => letI : NeZero (p' : ℕ) := ⟨p'.2.pos.ne'⟩; heckePic0Fibre k N (p' : ℕ)) h q' x


public theorem specialFibreHeckeModuleMatch_heckeModuleFibre [IsAlgClosed k]
    [AlgebraicCurve.IsCurveOver k (modularFunctionFieldC k N)]
    (h : HeckeOperatorsCommuteFibre k N data hKr) :
    SpecialFibreHeckeModuleMatch k N data hKr (heckeModuleFibre k N data hKr) :=
  specialFibreHeckeModuleMatch_heckeModuleFibreOf k N data hKr
    (fun p' => letI : NeZero (p' : ℕ) := ⟨p'.2.pos.ne'⟩; heckePic0Fibre k N (p' : ℕ)) h

end Instantiated

example : Prop :=
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  HeckeInputsFibre (ZMod 5) 7 2

example : Prop :=
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  HeckeDivFibreDescends (ZMod 5) 7 2

end ModularCurve

end
