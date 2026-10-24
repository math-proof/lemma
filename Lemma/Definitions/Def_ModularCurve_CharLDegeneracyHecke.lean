import Lemma.Definitions.Def_ModularCurve_CharLSpecialFibrePic0CommutingFamilyBridge

set_option autoImplicit false

noncomputable section

open AlgebraicCurve

namespace AlgebraicCurve

namespace Divisor

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

def DescendsToPic0 (T : Divisor K F →+ Divisor K F) : Prop :=
  (∀ D : Divisor K F, D ∈ Divisor.degZero (K := K) (F := F) → T D ∈ Divisor.degZero (K := K) (F := F)) ∧
    ∀ D : Divisor K F, D.IsPrincipal → (T D).IsPrincipal

def degZeroEnd (T : Divisor K F →+ Divisor K F) (h : DescendsToPic0 T) :
    Divisor.degZero (K := K) (F := F) →+ Divisor.degZero (K := K) (F := F) :=
  (T.domRestrict (Divisor.degZero (K := K) (F := F))).codRestrict _ (fun D => h.1 D D.2)

@[simp]
theorem coe_degZeroEnd (T : Divisor K F →+ Divisor K F) (h : DescendsToPic0 T)
    (D : Divisor.degZero (K := K) (F := F)) : (degZeroEnd T h D : Divisor K F) = T D :=
  rfl

open Classical in

def toPic0End (T : Divisor K F →+ Divisor K F) : Pic0 K F →+ Pic0 K F :=
  if h : DescendsToPic0 T then
    QuotientAddGroup.map _ _ (degZeroEnd T h) (by
      rintro ⟨D, hD0⟩ hD
      simp only [AddSubgroup.mem_addSubgroupOf] at hD ⊢
      exact h.2 D hD)
  else 0

theorem toPic0End_eq (T : Divisor K F →+ Divisor K F) (h : DescendsToPic0 T) :
    toPic0End T = QuotientAddGroup.map _ _ (degZeroEnd T h) (by
      rintro ⟨D, hD0⟩ hD
      simp only [AddSubgroup.mem_addSubgroupOf] at hD ⊢
      exact h.2 D hD) := by
  rw [toPic0End, dif_pos h]

theorem toPic0End_mk (T : Divisor K F →+ Divisor K F) (h : DescendsToPic0 T)
    (D : Divisor.degZero (K := K) (F := F)) :
    toPic0End T (Pic0.mk D) = Pic0.mk (degZeroEnd T h D) := by
  rw [toPic0End_eq T h]
  rfl

theorem toPic0End_of_not (T : Divisor K F →+ Divisor K F) (h : ¬ DescendsToPic0 T) : toPic0End T = 0 := by
  rw [toPic0End, dif_neg h]

end Divisor

end AlgebraicCurve

namespace ModularCurve

section CharSlot

variable (K : Type*) [Field K] (N : ℕ) [NeZero N] {ℓ : ℕ} [hℓ : Fact ℓ.Prime] [CharP K ℓ]
variable (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)

def heckePic0FibreChar : Module.End ℤ (Pic0 K (modularFunctionFieldC K N)) :=
  (Divisor.toPic0End (heckeFibreGeomLevel K N data hKr)).toIntLinearMap

theorem heckePic0FibreChar_apply (x : Pic0 K (modularFunctionFieldC K N)) :
    heckePic0FibreChar K N data hKr x = Divisor.toPic0End (heckeFibreGeomLevel K N data hKr) x :=
  rfl

theorem heckeFibreGeomLevel_indep (data' : ModularPolynomialData ℓ) (hKr' : KroneckerCongruence ℓ data') :
    heckeFibreGeomLevel K N data hKr = heckeFibreGeomLevel K N data' hKr' :=
  rfl

theorem heckePic0FibreChar_indep (data' : ModularPolynomialData ℓ) (hKr' : KroneckerCongruence ℓ data') :
    heckePic0FibreChar K N data hKr = heckePic0FibreChar K N data' hKr' :=
  rfl

theorem descendsToPic0_heckeFibreGeomLevel (hperf : ∀ c : K, ∃ d : K, d ^ ℓ = c)
    (hdeg1 : ∀ w : Place K (modularFunctionFieldC K N), w.deg = 1) :
    Divisor.DescendsToPic0 (heckeFibreGeomLevel K N data hKr) :=
  ⟨fun _ hD => heckeFibreGeomLevel_mem_degZero K N data hKr hdeg1 hD,
    fun _ hD => isPrincipal_heckeFibreGeomLevel' K N data hKr hperf
      (frobOnPlacesGeomLevel_surjective K N data hKr hperf) hD⟩

theorem heckePic0FibreChar_eq_heckeFibreGeomLevelPic0OfIsCurveOver [IsAlgClosed K]
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

def heckeFamilyFibreOf (q : Nat.Primes) : Module.End ℤ (Pic0 K (modularFunctionFieldC K N)) :=
  if (q : ℕ) = ℓ then heckePic0FibreChar K N data hKr else Tne q

theorem heckeFamilyFibreOf_of_eq {q : Nat.Primes} (hq : (q : ℕ) = ℓ) :
    heckeFamilyFibreOf K N data hKr Tne q = heckePic0FibreChar K N data hKr :=
  if_pos hq

theorem heckeFamilyFibreOf_of_ne {q : Nat.Primes} (hq : (q : ℕ) ≠ ℓ) :
    heckeFamilyFibreOf K N data hKr Tne q = Tne q :=
  if_neg hq

def HeckeOperatorsCommuteFibreOf : Prop :=
  ∀ q q' : Nat.Primes, Commute (heckeFamilyFibreOf K N data hKr Tne q) (heckeFamilyFibreOf K N data hKr Tne q')

variable {K N data hKr Tne} in

def heckeCommutingFamilyFibreOf (h : HeckeOperatorsCommuteFibreOf K N data hKr Tne) :
    CommutingHeckeFamily (Pic0 K (modularFunctionFieldC K N)) :=
  ⟨heckeFamilyFibreOf K N data hKr Tne, h⟩

open Classical in

@[implicit_reducible]
def heckeModuleFibreOf : Module HeckeAlg (Pic0 K (modularFunctionFieldC K N)) :=
  if h : HeckeOperatorsCommuteFibreOf K N data hKr Tne then (heckeCommutingFamilyFibreOf h).module
  else Module.compHom (Pic0 K (modularFunctionFieldC K N))
    (MvPolynomial.eval₂Hom (Int.castRingHom ℤ) (0 : Nat.Primes → ℤ))

variable {K N data hKr Tne}

theorem heckeModuleFibreOf_smul_def (h : HeckeOperatorsCommuteFibreOf K N data hKr Tne) (t : HeckeAlg)
    (x : Pic0 K (modularFunctionFieldC K N)) :
    (letI := heckeModuleFibreOf K N data hKr Tne; t • x) = (heckeCommutingFamilyFibreOf h).endHom t x := by
  have e : heckeModuleFibreOf K N data hKr Tne = (heckeCommutingFamilyFibreOf h).module := dif_pos h
  rw [e]
  rfl

theorem heckeModuleFibreOf_heckeGen_smul (h : HeckeOperatorsCommuteFibreOf K N data hKr Tne) (q : Nat.Primes)
    (x : Pic0 K (modularFunctionFieldC K N)) :
    (letI := heckeModuleFibreOf K N data hKr Tne; heckeGen q • x) = heckeFamilyFibreOf K N data hKr Tne q x := by
  rw [heckeModuleFibreOf_smul_def h, CommutingHeckeFamily.endHom_heckeGen]
  rfl

theorem heckeModuleFibreOf_heckeGen_smul_char (h : HeckeOperatorsCommuteFibreOf K N data hKr Tne) {q : Nat.Primes}
    (hq : (q : ℕ) = ℓ) (x : Pic0 K (modularFunctionFieldC K N)) :
    (letI := heckeModuleFibreOf K N data hKr Tne; heckeGen q • x) = heckePic0FibreChar K N data hKr x := by
  rw [heckeModuleFibreOf_heckeGen_smul h, heckeFamilyFibreOf_of_eq K N data hKr Tne hq]

theorem heckeModuleFibreOf_heckeGen_smul_of_ne (h : HeckeOperatorsCommuteFibreOf K N data hKr Tne) {q : Nat.Primes}
    (hq : (q : ℕ) ≠ ℓ) (x : Pic0 K (modularFunctionFieldC K N)) :
    (letI := heckeModuleFibreOf K N data hKr Tne; heckeGen q • x) = Tne q x := by
  rw [heckeModuleFibreOf_heckeGen_smul h, heckeFamilyFibreOf_of_ne K N data hKr Tne hq]

theorem heckeModuleFibreOf_smul_of_not (h : ¬ HeckeOperatorsCommuteFibreOf K N data hKr Tne) (t : HeckeAlg)
    (x : Pic0 K (modularFunctionFieldC K N)) :
    (letI := heckeModuleFibreOf K N data hKr Tne; t • x) = MvPolynomial.constantCoeff t • x := by
  have e : heckeModuleFibreOf K N data hKr Tne =
      Module.compHom (Pic0 K (modularFunctionFieldC K N))
        (MvPolynomial.eval₂Hom (Int.castRingHom ℤ) (0 : Nat.Primes → ℤ)) :=
    dif_neg h
  rw [e]
  show (MvPolynomial.eval₂Hom (Int.castRingHom ℤ) (0 : Nat.Primes → ℤ) t) • x = _
  rw [MvPolynomial.eval₂Hom_zero_apply, eq_intCast, Int.cast_id]

theorem heckeModuleFibreOf_heckeGen_smul_of_not (h : ¬ HeckeOperatorsCommuteFibreOf K N data hKr Tne)
    (q : Nat.Primes) (x : Pic0 K (modularFunctionFieldC K N)) :
    (letI := heckeModuleFibreOf K N data hKr Tne; heckeGen q • x) = 0 := by
  rw [heckeModuleFibreOf_smul_of_not h, heckeGen, MvPolynomial.constantCoeff_X, zero_zsmul]

private theorem endHom_C' {J' : Type*} [AddCommGroup J'] (fam : CommutingHeckeFamily J') (a : ℤ) :
    fam.endHom (MvPolynomial.C a) = (a : Module.End ℤ J') := by
  rw [← MvPolynomial.algebraMap_eq, eq_intCast, map_intCast]

theorem heckeModuleFibreOf_C_smul (a : ℤ) (x : Pic0 K (modularFunctionFieldC K N)) :
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

theorem pic0SpecialFibreCommutingFamilyMatch_heckeCommutingFamilyFibreOf
    (h : HeckeOperatorsCommuteFibreOf K N data hKr Tne) :
    Pic0SpecialFibreCommutingFamilyMatch K N data hKr (heckeCommutingFamilyFibreOf h) := by
  show heckeFamilyFibreOf K N data hKr Tne ⟨ℓ, hℓ.out⟩ = _
  rw [heckeFamilyFibreOf_of_eq K N data hKr Tne rfl,
    heckePic0FibreChar_eq_heckeFibreGeomLevelPic0OfIsCurveOver K N data hKr]

theorem specialFibreHeckeModuleMatch_heckeModuleFibreOf (h : HeckeOperatorsCommuteFibreOf K N data hKr Tne) :
    SpecialFibreHeckeModuleMatch K N data hKr (heckeModuleFibreOf K N data hKr Tne) := by
  have e : heckeModuleFibreOf K N data hKr Tne = (heckeCommutingFamilyFibreOf h).module := dif_pos h
  rw [e]
  exact specialFibreHeckeModuleMatch_of_commutingFamily K N data hKr _
    (pic0SpecialFibreCommutingFamilyMatch_heckeCommutingFamilyFibreOf K N data hKr Tne h)

end Match

end ModularCurve

namespace ModularCurve

variable (k : Type*) [Field k] (N q : ℕ) [NeZero N] [NeZero q]

def charLDegeneracyRoof : IntermediateField k (LaurentSeries k) :=
  IntermediateField.adjoin k
    {jqModC k, jqNModC k N, jqNModC k q, jqNModC k (N * q)}

theorem modularFunctionFieldC_le_charLDegeneracyRoof :
    modularFunctionFieldC k N ≤ charLDegeneracyRoof k N q := by
  unfold modularFunctionFieldC charLDegeneracyRoof
  apply IntermediateField.adjoin.mono
  intro x hx
  rcases hx with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

theorem qExpand_image_le_charLDegeneracyRoof :
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

def heckeAlphaC :
    modularFunctionFieldC k N →ₐ[k] charLDegeneracyRoof k N q :=
  IntermediateField.inclusion (modularFunctionFieldC_le_charLDegeneracyRoof k N q)

@[simp]
theorem coe_heckeAlphaC (x : modularFunctionFieldC k N) :
    (heckeAlphaC k N q x : LaurentSeries k) = (x : LaurentSeries k) :=
  IntermediateField.coe_inclusion _ x

def heckeBetaCRingHom :
    modularFunctionFieldC k N →+* charLDegeneracyRoof k N q where
  toFun x := ⟨qExpand k q (x : LaurentSeries k),
    qExpand_image_le_charLDegeneracyRoof k N q ⟨x, x.2, rfl⟩⟩
  map_one' := Subtype.ext (map_one (qExpand k q))
  map_mul' _ _ := Subtype.ext (map_mul (qExpand k q) _ _)
  map_zero' := Subtype.ext (map_zero (qExpand k q))
  map_add' _ _ := Subtype.ext (map_add (qExpand k q) _ _)

def heckeBetaC :
    modularFunctionFieldC k N →ₐ[k] charLDegeneracyRoof k N q :=
  { heckeBetaCRingHom k N q with
    commutes' := fun a => Subtype.ext <| by
      show qExpand k q (algebraMap k (LaurentSeries k) a) = algebraMap k (LaurentSeries k) a
      rw [algebraMap_laurentSeries_apply_eq_single, qExpand_single, mul_zero] }

@[simp]
theorem coe_heckeBetaC (x : modularFunctionFieldC k N) :
    (heckeBetaC k N q x : LaurentSeries k) = qExpand k q (x : LaurentSeries k) :=
  rfl

def HeckeAlphaCIntegral : Prop := (heckeAlphaC k N q).toRingHom.IsIntegral

def HeckeBetaCIntegral : Prop := (heckeBetaC k N q).toRingHom.IsIntegral

def heckeDivFibre [HasPrincipalDivisors k (charLDegeneracyRoof k N q)]
    (hβ : HeckeBetaCIntegral k N q) (hα : HeckeAlphaCIntegral k N q) :
    Divisor k (modularFunctionFieldC k N) →+ Divisor k (modularFunctionFieldC k N) :=
  Divisor.correspondence (heckeBetaC k N q) (heckeAlphaC k N q) hβ hα

def HeckeDivFibreDescends : Prop :=
  ∀ (hP : HasPrincipalDivisors k (charLDegeneracyRoof k N q))
    (hβ : HeckeBetaCIntegral k N q) (hα : HeckeAlphaCIntegral k N q),
    letI := hP
    AlgebraicCurve.Divisor.DescendsToPic0 (heckeDivFibre k N q hβ hα)

def HeckeInputsFibre : Prop :=
  ∃ (hP : HasPrincipalDivisors k (charLDegeneracyRoof k N q))
    (hβ : HeckeBetaCIntegral k N q) (hα : HeckeAlphaCIntegral k N q),
    letI := hP
    AlgebraicCurve.Divisor.DescendsToPic0 (heckeDivFibre k N q hβ hα)

open Classical in

def heckePic0Fibre : Module.End ℤ (Pic0 k (modularFunctionFieldC k N)) :=
  if h : HeckeInputsFibre k N q then
    letI := h.fst
    (AlgebraicCurve.Divisor.toPic0End (heckeDivFibre k N q h.snd.fst h.snd.snd.fst)).toIntLinearMap
  else 0

theorem heckeInputsFibre_intro
    [hP : HasPrincipalDivisors k (charLDegeneracyRoof k N q)]
    (hβ : HeckeBetaCIntegral k N q) (hα : HeckeAlphaCIntegral k N q)
    (hdesc : AlgebraicCurve.Divisor.DescendsToPic0 (heckeDivFibre k N q hβ hα)) :
    HeckeInputsFibre k N q :=
  ⟨hP, hβ, hα, hdesc⟩

theorem heckePic0Fibre_eq
    [hP : HasPrincipalDivisors k (charLDegeneracyRoof k N q)]
    (hβ : HeckeBetaCIntegral k N q) (hα : HeckeAlphaCIntegral k N q)
    (hdesc : AlgebraicCurve.Divisor.DescendsToPic0 (heckeDivFibre k N q hβ hα)) :
    heckePic0Fibre k N q
      = (AlgebraicCurve.Divisor.toPic0End (heckeDivFibre k N q hβ hα)).toIntLinearMap := by
  rw [heckePic0Fibre, dif_pos (heckeInputsFibre_intro k N q hβ hα hdesc)]

theorem heckePic0Fibre_of_not (h : ¬ HeckeInputsFibre k N q) : heckePic0Fibre k N q = 0 := by
  rw [heckePic0Fibre, dif_neg h]

section Instantiated

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] [CharP k ℓ]
  (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)

def heckeFamilyFibre (q' : Nat.Primes) : Module.End ℤ (Pic0 k (modularFunctionFieldC k N)) :=
  heckeFamilyFibreOf k N data hKr
    (fun p' => letI : NeZero (p' : ℕ) := ⟨p'.2.pos.ne'⟩; heckePic0Fibre k N (p' : ℕ)) q'

def HeckeOperatorsCommuteFibre : Prop :=
  HeckeOperatorsCommuteFibreOf k N data hKr
    (fun p' => letI : NeZero (p' : ℕ) := ⟨p'.2.pos.ne'⟩; heckePic0Fibre k N (p' : ℕ))

@[implicit_reducible]
def heckeModuleFibre : Module HeckeAlg (Pic0 k (modularFunctionFieldC k N)) :=
  heckeModuleFibreOf k N data hKr
    (fun p' => letI : NeZero (p' : ℕ) := ⟨p'.2.pos.ne'⟩; heckePic0Fibre k N (p' : ℕ))

theorem heckeModuleFibre_heckeGen_smul (h : HeckeOperatorsCommuteFibre k N data hKr)
    (q' : Nat.Primes) (x : Pic0 k (modularFunctionFieldC k N)) :
    (letI := heckeModuleFibre k N data hKr; heckeGen q' • x)
      = heckeFamilyFibre k N data hKr q' x :=
  heckeModuleFibreOf_heckeGen_smul (K := k) (N := N) (data := data) (hKr := hKr)
    (Tne := fun p' => letI : NeZero (p' : ℕ) := ⟨p'.2.pos.ne'⟩; heckePic0Fibre k N (p' : ℕ)) h q' x

theorem specialFibreHeckeModuleMatch_heckeModuleFibre [IsAlgClosed k]
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
