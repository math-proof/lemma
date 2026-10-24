import Lemma.Definitions.Def_WeierstrassCurve_ReductionMap
import Lemma.Definitions.Def_AlgebraicCurve_ConstantReduction
import Lemma.Definitions.Def_AlgebraicCurve_PlaceEvaluation

set_option autoImplicit false

noncomputable section

open AlgebraicCurve

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

theorem mem_nuBall_iff (a : ↥L) : a ∈ nuBall L ν ↔ ν a ≤ 1 := Iff.rfl

theorem isUnit_nuBall_iff (a : ↥L) (ha : ν a ≤ 1) :
    IsUnit (⟨a, ha⟩ : nuBall L ν) ↔ ν a = 1 := by
  constructor
  · rintro ⟨u, hu⟩
    have h1 : (↑u : nuBall L ν) * ↑u⁻¹ = 1 := u.mul_inv
    have h2 : ((↑u : nuBall L ν) : ↥L) * ((↑u⁻¹ : nuBall L ν) : ↥L) = 1 :=
      congrArg Subtype.val h1
    have ha' : ((↑u : nuBall L ν) : ↥L) = a := congrArg Subtype.val hu
    have hb : ν ((↑u⁻¹ : nuBall L ν) : ↥L) ≤ 1 := (↑u⁻¹ : nuBall L ν).2
    have hνmul : ν a * ν ((↑u⁻¹ : nuBall L ν) : ↥L) = 1 := by
      rw [← ha', ← map_mul, h2, map_one]
    refine le_antisymm ha ?_
    calc (1 : ℝ) = ν a * ν ((↑u⁻¹ : nuBall L ν) : ↥L) := hνmul.symm
      _ ≤ ν a * 1 := mul_le_mul_of_nonneg_left hb (apply_nonneg ν a)
      _ = ν a := mul_one _
  · intro h1
    have hane : a ≠ 0 := by
      intro h0
      rw [h0, map_zero] at h1
      exact zero_ne_one h1
    have hinv : ν a⁻¹ ≤ 1 := by
      have h : ν a⁻¹ = (ν a)⁻¹ := map_inv₀ ν a
      rw [h, h1]
      norm_num
    refine isUnit_iff_exists_inv.mpr ⟨⟨a⁻¹, hinv⟩, ?_⟩
    exact Subtype.ext (mul_inv_cancel₀ hane)

end NuBall

structure FinitePlaceLift (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥L]
    (ν : NumberField.FinitePlace ↥L) : Type where

  A : ValuationSubring (AlgebraicClosure ℚ)

  mem_iff : ∀ a : ↥L, (↑a : AlgebraicClosure ℚ) ∈ A ↔ ν a ≤ 1

  p : ℕ

  pprime : p.Prime

  lies : A.LiesOverPrime p

namespace FinitePlaceLift

variable {L : IntermediateField ℚ (AlgebraicClosure ℚ)} [NumberField ↥L]
  {ν : NumberField.FinitePlace ↥L} (M : FinitePlaceLift L ν)

theorem isUnit_mk_iff (a : ↥L) (hmem : (↑a : AlgebraicClosure ℚ) ∈ M.A) :
    IsUnit (⟨↑a, hmem⟩ : M.A) ↔ ν a = 1 := by
  constructor
  · rintro ⟨u, hu⟩
    have h1 : (↑u : M.A) * ↑u⁻¹ = 1 := u.mul_inv
    have h2 : ((↑u : M.A) : AlgebraicClosure ℚ) * ((↑u⁻¹ : M.A) : AlgebraicClosure ℚ) = 1 :=
      congrArg Subtype.val h1
    have ha' : ((↑u : M.A) : AlgebraicClosure ℚ) = (↑a : AlgebraicClosure ℚ) :=
      congrArg Subtype.val hu
    have hane : a ≠ 0 := by
      intro h0
      rw [ha', h0] at h2
      have : ((0 : ↥L) : AlgebraicClosure ℚ) = 0 := rfl
      rw [this, zero_mul] at h2
      exact zero_ne_one h2
    have hbinv : ((↑u⁻¹ : M.A) : AlgebraicClosure ℚ) = ((a⁻¹ : ↥L) : AlgebraicClosure ℚ) := by
      have hcoeinv : ((a⁻¹ : ↥L) : AlgebraicClosure ℚ) = ((a : ↥L) : AlgebraicClosure ℚ)⁻¹ := by
        push_cast
        rfl
      rw [hcoeinv, ← ha']
      exact (inv_eq_of_mul_eq_one_right h2).symm
    have hmeminv : ((a⁻¹ : ↥L) : AlgebraicClosure ℚ) ∈ M.A := by
      rw [← hbinv]
      exact (↑u⁻¹ : M.A).2
    have hle : ν a ≤ 1 := (M.mem_iff a).mp hmem
    have hinvle : ν a⁻¹ ≤ 1 := (M.mem_iff a⁻¹).mp hmeminv
    have hinv : ν a⁻¹ = (ν a)⁻¹ := map_inv₀ ν a
    rw [hinv] at hinvle
    have hpos : 0 < ν a := by
      rcases (apply_nonneg ν a).lt_or_eq with h | h
      · exact h
      · exfalso
        have : ν a = 0 := h.symm
        rw [map_eq_zero] at this
        exact hane this
    have hge : 1 ≤ ν a := by
      rw [inv_le_one_iff₀] at hinvle
      rcases hinvle with h | h
      · exact absurd (lt_of_le_of_lt h hpos) (lt_irrefl _)
      · exact h
    exact le_antisymm hle hge
  · intro h1
    have hane : a ≠ 0 := by
      intro h0
      rw [h0, map_zero] at h1
      exact zero_ne_one h1
    have hinvle : ν a⁻¹ ≤ 1 := by
      have h : ν a⁻¹ = (ν a)⁻¹ := map_inv₀ ν a
      rw [h, h1]
      norm_num
    have hmeminv : ((a⁻¹ : ↥L) : AlgebraicClosure ℚ) ∈ M.A := (M.mem_iff a⁻¹).mpr hinvle
    refine isUnit_iff_exists_inv.mpr ⟨⟨_, hmeminv⟩, ?_⟩
    apply Subtype.ext
    show (↑a : AlgebraicClosure ℚ) * ((a⁻¹ : ↥L) : AlgebraicClosure ℚ)
        = ((1 : M.A) : AlgebraicClosure ℚ)
    have hmul : ((a * a⁻¹ : ↥L) : AlgebraicClosure ℚ) = ((1 : ↥L) : AlgebraicClosure ℚ) :=
      congrArg (fun x : ↥L => (x : AlgebraicClosure ℚ)) (mul_inv_cancel₀ hane)
    have hsplit : ((a * a⁻¹ : ↥L) : AlgebraicClosure ℚ)
        = (↑a : AlgebraicClosure ℚ) * ((a⁻¹ : ↥L) : AlgebraicClosure ℚ) := rfl
    rw [← hsplit, hmul]
    rfl

theorem mem_maximalIdeal_iff (a : ↥L) (hmem : (↑a : AlgebraicClosure ℚ) ∈ M.A) :
    (⟨↑a, hmem⟩ : M.A) ∈ IsLocalRing.maximalIdeal ↥M.A ↔ ν a < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  have hle : ν a ≤ 1 := (M.mem_iff a).mp hmem
  constructor
  · intro hnu
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exact absurd ((M.isUnit_mk_iff a hmem).mpr h) hnu
  · intro hlt hu
    exact hlt.ne ((M.isUnit_mk_iff a hmem).mp hu)

theorem charP_residueField : CharP (IsLocalRing.ResidueField ↥M.A) M.p :=
  ValuationSubring.charP_residueField_of_liesOverPrime_def M.pprime M.lies

theorem nu_p_lt_one : ν ((M.p : ℕ) : ↥L) < 1 := by
  have hcast : (((M.p : ℕ) : ↥L) : AlgebraicClosure ℚ) = ((M.p : ℕ) : AlgebraicClosure ℚ) := by
    push_cast
    rfl
  have hmem : (((M.p : ℕ) : ↥L) : AlgebraicClosure ℚ) ∈ M.A := by
    rw [hcast]
    exact_mod_cast SetLike.coe_mem (((M.p : ℕ) : M.A))
  have hmax := ValuationSubring.natCast_mem_maximalIdeal_of_liesOverPrime (A := M.A) M.lies
  have helt : (((M.p : ℕ) : M.A)) = (⟨↑((M.p : ℕ) : ↥L), hmem⟩ : M.A) := by
    apply Subtype.ext
    show ((M.p : ℕ) : AlgebraicClosure ℚ) = (((M.p : ℕ) : ↥L) : AlgebraicClosure ℚ)
    · exact hcast.symm
  rw [helt] at hmax
  exact (M.mem_maximalIdeal_iff _ hmem).mp hmax

theorem mem_maximalIdeal_nuBall_iff (a : ↥(nuBall L ν)) :
    a ∈ IsLocalRing.maximalIdeal ↥(nuBall L ν) ↔ ν ↑a < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  have hle : ν ↑a ≤ 1 := a.2
  constructor
  · intro hnu
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exact absurd ((isUnit_nuBall_iff L ν ↑a hle).mpr h) (by
        intro hu
        apply hnu
        have : (⟨↑a, hle⟩ : nuBall L ν) = a := Subtype.ext rfl
        rwa [this] at hu)
  · intro hlt hu
    have : IsUnit (⟨↑a, hle⟩ : nuBall L ν) := by
      have heq : (⟨↑a, hle⟩ : nuBall L ν) = a := Subtype.ext rfl
      rwa [heq]
    exact hlt.ne ((isUnit_nuBall_iff L ν ↑a hle).mp this)

noncomputable def traceHom (M : FinitePlaceLift L ν) : ↥(nuBall L ν) →+* ↥M.A where
  toFun a := ⟨↑↑a, (M.mem_iff ↑a).mpr a.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem traceHom_coe (M : FinitePlaceLift L ν) (a : ↥(nuBall L ν)) :
    ((M.traceHom a : ↥M.A) : AlgebraicClosure ℚ) = ((↑a : ↥L) : AlgebraicClosure ℚ) := rfl

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

theorem residueFieldEmb_residue (M : FinitePlaceLift L ν) (a : ↥(nuBall L ν)) :
    M.residueFieldEmb (IsLocalRing.residue _ a) = IsLocalRing.residue ↥M.A (M.traceHom a) :=
  rfl

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

theorem mem_nuBallOpen_iff (a : ↥(nuBall L ν)) : a ∈ nuBallOpen L ν ↔ ν ↑a < 1 := Iff.rfl

noncomputable def constIncl : ↥L →+* AlgebraicClosure ℚ := algebraMap ↥L (AlgebraicClosure ℚ)

omit [NumberField ↥L] in
theorem constIncl_injective : Function.Injective (constIncl L) := (constIncl L).injective

noncomputable def ballEquivQbar :
    ↥(nuBall L ν).toSubring ≃+* ↥((nuBall L ν).toSubring.map (constIncl L)) :=
  Subring.equivMapOfInjective (nuBall L ν).toSubring (constIncl L) (constIncl_injective L)

theorem exists_valuationSubring_trace_eq :
    ∃ B : ValuationSubring (AlgebraicClosure ℚ),
      ∀ a : ↥L, (↑a : AlgebraicClosure ℚ) ∈ B ↔ ν a ≤ 1 := by
  classical
  set A₀ : Subring (AlgebraicClosure ℚ) := (nuBall L ν).toSubring.map (constIncl L) with hA₀
  set I : Ideal A₀ := Ideal.map (ballEquivQbar L ν).toRingHom (nuBallOpen L ν) with hI
  have hInetop : I ≠ ⊤ := by
    intro htop
    have h1 : (1 : A₀) ∈ I := htop ▸ Submodule.mem_top
    have hcomap : ((1 : ↥(nuBall L ν).toSubring)) ∈ nuBallOpen L ν := by
      have hcm := Ideal.comap_map_of_bijective (ballEquivQbar L ν).toRingHom
        (ballEquivQbar L ν).bijective (I := nuBallOpen L ν)
      rw [← hcm]
      refine Ideal.mem_comap.mpr ?_
      rw [map_one]
      exact h1
    have : ν ((1 : ↥(nuBall L ν).toSubring) : ↥L) < 1 := hcomap
    rw [show ((1 : ↥(nuBall L ν).toSubring) : ↥L) = 1 from rfl, map_one] at this
    exact lt_irrefl 1 this
  obtain ⟨B, hle, hnon⟩ := Ideal.image_subset_nonunits_valuationSubring I hInetop
  refine ⟨B, fun a => ⟨?_, ?_⟩⟩
  ·
    intro hmem
    by_contra hgt
    rw [not_le] at hgt
    have hane : a ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hgt
      exact absurd hgt (by norm_num)
    have hinvlt : ν a⁻¹ < 1 := by
      have h : ν a⁻¹ = (ν a)⁻¹ := map_inv₀ ν a
      rw [h]
      exact inv_lt_one_of_one_lt₀ hgt
    have hinvmem : (⟨a⁻¹, le_of_lt hinvlt⟩ : ↥(nuBall L ν).toSubring) ∈ nuBallOpen L ν :=
      hinvlt
    have himg : (constIncl L) a⁻¹ ∈ A₀.subtype '' ↑I := by
      refine ⟨(ballEquivQbar L ν).toRingHom ⟨a⁻¹, le_of_lt hinvlt⟩, ?_, ?_⟩
      · exact Ideal.mem_map_of_mem _ hinvmem
      · rfl
    have hnonu : (constIncl L) a⁻¹ ∈ B.nonunits := hnon himg
    have hinveq : (constIncl L) a⁻¹ = ((↑a : AlgebraicClosure ℚ))⁻¹ := by
      show ((a⁻¹ : ↥L) : AlgebraicClosure ℚ) = ((↑a : AlgebraicClosure ℚ))⁻¹
      push_cast
      rfl
    rw [hinveq] at hnonu
    have hane' : (↑a : AlgebraicClosure ℚ) ≠ 0 := fun h0 => hane (by exact_mod_cast h0)
    have := (B.inv_mem_nonunits_iff.mp hnonu).resolve_left hane'
    exact this hmem
  ·
    intro ha
    have : (↑a : AlgebraicClosure ℚ) ∈ A₀ := Subring.mem_map.mpr ⟨a, ha, rfl⟩
    exact hle this

theorem exists_prime_nu_lt_one : ∃ q : ℕ, q.Prime ∧ ν ((q : ℕ) : ↥L) < 1 := by
  classical
  obtain ⟨q, n, hn, hqP, hq, -⟩ :=
    Ideal.exists_prime_and_absNorm_eq_pow (NumberField.FinitePlace.maximalIdeal ν).asIdeal
  refine ⟨q, hq, ?_⟩
  have hlt := (NumberField.FinitePlace.norm_lt_one_iff_mem ↥L
    (NumberField.FinitePlace.maximalIdeal ν)
    ((q : ℕ) : NumberField.RingOfIntegers ↥L)).mpr hqP
  rw [NumberField.FinitePlace.norm_embedding_eq, map_natCast] at hlt
  exact hlt

theorem exists_finitePlaceLift : Nonempty (FinitePlaceLift L ν) := by
  classical
  obtain ⟨B, hB⟩ := exists_valuationSubring_trace_eq L ν
  obtain ⟨q, hq, hqlt⟩ := exists_prime_nu_lt_one L ν
  have hqne : ((q : ℕ) : ↥L) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
  have hqpos : 0 < ν ((q : ℕ) : ↥L) := NumberField.FinitePlace.pos_iff.mpr hqne
  refine ⟨⟨B, hB, q, hq, ?_⟩⟩
  rw [ValuationSubring.liesOverPrime_iff]
  have hqQne : ((q : ℕ) : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
  have hinv_notmem : (((q : ℕ) : AlgebraicClosure ℚ))⁻¹ ∉ B := by
    intro hmem
    have hcoe : ((((q : ℕ) : ↥L))⁻¹ : AlgebraicClosure ℚ)
        = (((q : ℕ) : AlgebraicClosure ℚ))⁻¹ := by
      push_cast
      rfl
    have hmem' : ((((q : ℕ) : ↥L))⁻¹ : AlgebraicClosure ℚ) ∈ B := by
      rw [hcoe]
      exact hmem
    have hle : ν (((q : ℕ) : ↥L))⁻¹ ≤ 1 := (hB _).mp hmem'
    have hgt : 1 < ν (((q : ℕ) : ↥L))⁻¹ := by
      have h : ν (((q : ℕ) : ↥L))⁻¹ = (ν ((q : ℕ) : ↥L))⁻¹ := map_inv₀ ν _
      rw [h]
      exact (one_lt_inv₀ hqpos).mpr hqlt
    exact absurd hle (not_le.mpr hgt)
  rw [show ((q : ℕ) : AlgebraicClosure ℚ) = (((q : ℕ) : AlgebraicClosure ℚ))⁻¹⁻¹ from
    (inv_inv _).symm]
  exact B.inv_mem_nonunits_iff.mpr (Or.inr hinv_notmem)

end Existence

theorem nonempty_finitePlaceLift (L : IntermediateField ℚ (AlgebraicClosure ℚ))
    [NumberField ↥L] (ν : NumberField.FinitePlace ↥L) : Nonempty (FinitePlaceLift L ν) :=
  exists_finitePlaceLift L ν

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

private theorem maximalIdeal_top_eq_bot (X : Type*) [Field X] :
    IsLocalRing.maximalIdeal ↥(⊤ : ValuationSubring X) = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro x hx
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx
  rw [Ideal.mem_bot]
  by_contra hne
  apply hx
  have hxv : (x : X) ≠ 0 := fun h => hne (Subtype.ext h)
  exact ⟨⟨x, ⟨(x : X)⁻¹, ValuationSubring.mem_top _⟩,
    Subtype.ext (mul_inv_cancel₀ hxv), Subtype.ext (inv_mul_cancel₀ hxv)⟩, rfl⟩

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

private theorem residueTopEquiv_residue (a : ↥(⊤ : ValuationSubring L)) :
    residueTopEquiv L (IsLocalRing.residue _ a) = (a : L) := rfl

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

private theorem placeMapOfTop_injective : Function.Injective (placeMapOfTop L F) :=
  fun _ _ h => Place.ext (congrArg
    (fun Q : Place (ResidueField ↥(⊤ : ValuationSubring L)) F => Q.toValuationSubring) h)

private theorem placeMapOfTop_surjective : Function.Surjective (placeMapOfTop L F) := by
  intro Q
  refine ⟨⟨Q.toValuationSubring, fun a => ?_, Q.ne_top', Q.isPrincipalIdealRing'⟩,
    Place.ext rfl⟩
  have h1 : algebraMap L F a
      = algebraMap (ResidueField ↥(⊤ : ValuationSubring L)) F
        ((residueTopEquiv L).symm a) := by
    show _ = ((algebraMap L F).comp (residueTopEquiv L).toRingHom) _
    simp
  rw [h1]
  exact Q.algebraMap_mem' _

private theorem ord_placeMapOfTop (P : Place L F) (f : F) :
    (placeMapOfTop L F P).ord f = P.ord f := rfl

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
    classical
    obtain ⟨Q₀, rfl⟩ := placeMapOfTop_surjective L F Q
    rw [Finsupp.mapDomain_apply (placeMapOfTop_injective L F), hD Q₀,
      ord_placeMapOfTop]
    rfl

theorem isPointwise_ofTop_of_isEmpty [IsEmpty (Place L F)] : (ofTop L F).IsPointwise :=
  fun P => isEmptyElim P

theorem isEmpty_place_self : IsEmpty (Place L L) :=
  ⟨fun P => P.ne_top' (by
    ext x
    simp only [ValuationSubring.mem_top, iff_true]
    exact P.algebraMap_mem' x)⟩

theorem isPointwise_ofTop_self : (ofTop L L).IsPointwise :=
  haveI : IsEmpty (Place L L) := isEmpty_place_self L
  isPointwise_ofTop_of_isEmpty L L

theorem exists_isDiscParam_ofTop (v : Place L F) :
    ∃ T : F, (ofTop L F).IsDiscParam v T := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (R := v.toValuationSubring)
  refine ⟨(π : F), ValuationSubring.mem_top _, fun h0 => hπ.ne_zero (Subtype.ext ?_), ?_, ?_, ?_⟩
  · exact h0
  · show (placeMapOfTop L F v).ord (π : F) = 1
    rw [ord_placeMapOfTop]
    exact v.ord_coe_irreducible hπ
  · rw [v.ord_coe_irreducible hπ]
    exact zero_lt_one
  · intro Q hQ
    have hQv : Q = v := placeMapOfTop_injective L F hQ
    rw [hQv, v.ord_coe_irreducible hπ]
    exact zero_le_one

theorem isPointwise_ofTop (L : Type*) [Field L] (F : Type*) [Field F] [Algebra L F] :
    (ofTop L F).IsPointwise := by
  intro P hP f hf hfib
  have hfP : f ∈ P.toValuationSubring := hfib P rfl
  refine ⟨hfP, ValuationSubring.mem_top _, ?_⟩
  · show algebraMap _ _ (IsLocalRing.residue _ (⟨P.evalAt f, ValuationSubring.mem_top _⟩ :
        ↥(⊤ : ValuationSubring L)))
      = IsLocalRing.residue _ (⟨f, hfP⟩ : (placeMapOfTop L F P).toValuationSubring)
    exact P.algebraMap_evalAt hP hfP

end DegenerateMember

end ConstantReduction

end AlgebraicCurve
