import Lemma.Scheme.CharLSpecialFibrePic0CommutingFamilyBridge

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

open Classical in

def toPic0End (T : Divisor K F →+ Divisor K F) : Pic0 K F →+ Pic0 K F :=
  if h : DescendsToPic0 T then
    QuotientAddGroup.map _ _ (degZeroEnd T h) (by
      rintro ⟨D, hD0⟩ hD
      simp only [AddSubgroup.mem_addSubgroupOf] at hD ⊢
      exact h.2 D hD)
  else 0

end Divisor

end AlgebraicCurve

namespace ModularCurve

section CharSlot

variable (K : Type*) [Field K] (N : ℕ) [NeZero N] {ℓ : ℕ} [hℓ : Fact ℓ.Prime] [CharP K ℓ]
variable (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)

def heckePic0FibreChar : Module.End ℤ (Pic0 K (modularFunctionFieldC K N)) :=
  (Divisor.toPic0End (heckeFibreGeomLevel K N data hKr)).toIntLinearMap

end CharSlot

section Family

variable (K : Type*) [Field K] (N : ℕ) [NeZero N] {ℓ : ℕ} [hℓ : Fact ℓ.Prime] [CharP K ℓ]
variable (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)
variable (Tne : Nat.Primes → Module.End ℤ (Pic0 K (modularFunctionFieldC K N)))

def heckeFamilyFibreOf (q : Nat.Primes) : Module.End ℤ (Pic0 K (modularFunctionFieldC K N)) :=
  if (q : ℕ) = ℓ then heckePic0FibreChar K N data hKr else Tne q

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

end Family


end ModularCurve

namespace ModularCurve

variable (k : Type*) [Field k] (N q : ℕ) [NeZero N] [NeZero q]

def charLDegeneracyRoof : IntermediateField k (LaurentSeries k) :=
  IntermediateField.adjoin k
    {jqModC k, jqNModC k N, jqNModC k q, jqNModC k (N * q)}

def heckeAlphaC :
    modularFunctionFieldC k N →ₐ[k] charLDegeneracyRoof k N q :=
  IntermediateField.inclusion (modularFunctionFieldC_le_charLDegeneracyRoof k N q)

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

end Instantiated

end ModularCurve

end
