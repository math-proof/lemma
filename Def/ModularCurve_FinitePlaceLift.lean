import Def.WeierstrassCurve_ReductionMap
import Def.AlgebraicCurve_ConstantReduction
import Def.AlgebraicCurve_PlaceEvaluation
import Structure.ModularCurve_FinitePlaceLift

set_option autoImplicit false

noncomputable section

open AlgebraicCurve ResidueField

namespace ModularCurve

section NuBall

variable (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥L]
  (ν : NumberField.FinitePlace ↥L)

noncomputable def nuBall : ValuationSubring ↥L where
  carrier := {a | ν a ≤ 1}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    have h : ν (a * b) = ν a * ν b := map_mul ν a b
    calc ν (a * b) = ν a * ν b := h
      _ ≤ 1 * 1 := mul_le_mul ha hb (apply_nonneg ν b) zero_le_one
      _ = 1 := one_mul 1
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    exact (ν.add_le a b).trans (max_le ha hb)
  neg_mem' := by
    intro a ha
    have h : ν (-a) = ν a := ν.val.map_neg a
    show ν (-a) ≤ 1
    rw [h]
    exact ha
  mem_or_inv_mem' := by
    intro a
    rcases le_total (ν a) 1 with h | h
    · exact Or.inl h
    · right
      show ν a⁻¹ ≤ 1
      have hinv : ν a⁻¹ = (ν a)⁻¹ := map_inv₀ ν a
      rw [hinv]
      exact inv_le_one_of_one_le₀ h

end NuBall


namespace FinitePlaceLift

variable {L : IntermediateField ℚ (AlgebraicClosure ℚ)} [NumberField ↥L]
  {ν : NumberField.FinitePlace ↥L} (M : FinitePlaceLift L ν)

noncomputable def traceHom (M : FinitePlaceLift L ν) : ↥(nuBall L ν) →+* ↥M.A where
  toFun a := ⟨↑↑a, (M.mem_iff ↑a).mpr a.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

noncomputable def residueFieldEmb (M : FinitePlaceLift L ν) :
    IsLocalRing.ResidueField ↥(nuBall L ν) →+* IsLocalRing.ResidueField ↥M.A :=
  Ideal.Quotient.lift (IsLocalRing.maximalIdeal ↥(nuBall L ν))
    ((IsLocalRing.residue ↥M.A).comp M.traceHom)
    (by
      intro a ha
      have hlt : ν ↑a < 1 := (mem_maximalIdeal_nuBall_iff a).mp ha
      have hmem' : ((↑a : ↥L) : AlgebraicClosure ℚ) ∈ M.A := (M.mem_iff ↑a).mpr a.2
      have : M.traceHom a ∈ IsLocalRing.maximalIdeal ↥M.A := by
        have heq : M.traceHom a = (⟨↑↑a, hmem'⟩ : M.A) := Subtype.ext rfl
        rw [heq]
        exact (M.mem_maximalIdeal_iff ↑a hmem').mpr hlt
      rw [RingHom.comp_apply]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr this)

end FinitePlaceLift

section Existence

variable (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥L]
  (ν : NumberField.FinitePlace ↥L)

noncomputable def nuBallOpen : Ideal ↥(nuBall L ν) where
  carrier := {a | ν ↑a < 1}
  zero_mem' := by
    show ν ((0 : nuBall L ν) : ↥L) < 1
    rw [show ((0 : nuBall L ν) : ↥L) = 0 from rfl, map_zero]
    exact zero_lt_one
  add_mem' := by
    intro a b ha hb
    show ν ((a + b : nuBall L ν) : ↥L) < 1
    have h : ((a + b : nuBall L ν) : ↥L) = ↑a + ↑b := rfl
    rw [h]
    exact lt_of_le_of_lt (ν.add_le _ _) (max_lt ha hb)
  smul_mem' := by
    intro c a ha
    show ν ((c * a : nuBall L ν) : ↥L) < 1
    have h : ((c * a : nuBall L ν) : ↥L) = ↑c * ↑a := rfl
    rw [h, map_mul]
    calc ν ↑c * ν ↑a ≤ 1 * ν ↑a := mul_le_mul_of_nonneg_right c.2 (apply_nonneg ν _)
      _ = ν ↑a := one_mul _
      _ < 1 := ha

noncomputable def constIncl : ↥L →+* AlgebraicClosure ℚ := algebraMap ↥L (AlgebraicClosure ℚ)

omit [NumberField ↥L] in
noncomputable def ballEquivQbar :
    ↥(nuBall L ν).toSubring ≃+* ↥((nuBall L ν).toSubring.map (constIncl L)) :=
  Subring.equivMapOfInjective (nuBall L ν).toSubring (constIncl L) (constIncl_injective L)

end Existence

end ModularCurve

namespace AlgebraicCurve

open IsLocalRing

variable {K : Type*} [Field K] {A : ValuationSubring K}
variable {F : Type*} [Field F] [Algebra K F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

namespace ConstantReduction

def IsPointwise (R : ConstantReduction A F Fbar) : Prop :=
  ∀ P : Place K F, P.IsRational → ∀ (f : F) (hf : f ∈ R.integers),
    (∀ w : Place K F, R.placeMap w = R.placeMap P → f ∈ w.toValuationSubring) →
      ∃ (hm : (R.residue ⟨f, hf⟩ : Fbar) ∈ (R.placeMap P).toValuationSubring)
        (h : P.evalAt f ∈ A),
        algebraMap (ResidueField A) (R.placeMap P).ResidueField
            (IsLocalRing.residue A ⟨P.evalAt f, h⟩)
          = IsLocalRing.residue (R.placeMap P).toValuationSubring ⟨R.residue ⟨f, hf⟩, hm⟩

def IsDiscParam (R : ConstantReduction A F Fbar) (P : Place K F) (T : F) : Prop :=
  ∃ hT : T ∈ R.integers, R.residue ⟨T, hT⟩ ≠ 0 ∧ (R.placeMap P).ord (R.residue ⟨T, hT⟩) = 1 ∧
    0 < P.ord T ∧ ∀ Q : Place K F, R.placeMap Q = R.placeMap P → 0 ≤ Q.ord T

section DegenerateMember

variable (L : Type*) [Field L] (F : Type*) [Field F] [Algebra L F]

private noncomputable def residueTopEquiv : ResidueField ↥(⊤ : ValuationSubring L) ≃+* L :=
  RingEquiv.ofBijective
    (Ideal.Quotient.lift (IsLocalRing.maximalIdeal ↥(⊤ : ValuationSubring L))
      (⊤ : ValuationSubring L).subtype
      (fun a ha => by
        rw [maximalIdeal_top_eq_bot, Ideal.mem_bot] at ha
        rw [ha]
        rfl))
    ⟨RingHom.injective _,
     fun x => ⟨Ideal.Quotient.mk _ ⟨x, ValuationSubring.mem_top _⟩,
      Ideal.Quotient.lift_mk (IsLocalRing.maximalIdeal ↥(⊤ : ValuationSubring L)) _ _⟩⟩

@[reducible] noncomputable def ofTopAlgebra :
    Algebra (ResidueField ↥(⊤ : ValuationSubring L)) F :=
  ((algebraMap L F).comp (residueTopEquiv L).toRingHom).toAlgebra

attribute [local instance] ofTopAlgebra

private noncomputable def placeMapOfTop (P : Place L F) :
    Place (ResidueField ↥(⊤ : ValuationSubring L)) F where
  toValuationSubring := P.toValuationSubring
  algebraMap_mem' := fun a => by
    show ((algebraMap L F).comp (residueTopEquiv L).toRingHom) a ∈ _
    exact P.algebraMap_mem' _
  ne_top' := P.ne_top'
  isPrincipalIdealRing' := P.isPrincipalIdealRing'

noncomputable def ofTop : ConstantReduction (⊤ : ValuationSubring L) F F where
  integers := ⊤
  residue := (⊤ : ValuationSubring F).subtype
  placeMap := placeMapOfTop L F
  algebraMap_mem_iff := fun x =>
    ⟨fun _ => ValuationSubring.mem_top _, fun _ => ValuationSubring.mem_top _⟩
  residue_surjective := fun y => ⟨⟨y, ValuationSubring.mem_top _⟩, rfl⟩
  ker_residue := by
    rw [maximalIdeal_top_eq_bot]
    ext x
    simp only [RingHom.mem_ker, Ideal.mem_bot]
    exact ⟨fun h => Subtype.ext h, fun h => by rw [h]; rfl⟩
  residue_algebraMap := fun a => by
    show algebraMap L F (a : L)
        = ((algebraMap L F).comp (residueTopEquiv L).toRingHom) (IsLocalRing.residue _ a)
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
    rw [residueTopEquiv_residue]
  exists_smul_mem := fun f hf => by
    refine ⟨1, ValuationSubring.mem_top _, fun h0 => hf ?_⟩
    have h1 : (1 : L) • f = 0 := h0
    rwa [one_smul] at h1
  deg_placeMap := fun P => by
    show Module.finrank (ResidueField ↥(⊤ : ValuationSubring L)) _ = Module.finrank L _
    exact Algebra.finrank_eq_of_equiv_equiv (residueTopEquiv L) (RingEquiv.refl _)
      (by ext a; rfl)
  mapDomain_placeMap := fun f hres D hD Q => by
end DegenerateMember

end ConstantReduction

end AlgebraicCurve

end
