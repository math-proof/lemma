module

public import Theorem.WeierstrassCurve.ReductionMap
public import Theorem.ResidueField.ConstantReduction
public import Def.AlgebraicCurve_PlaceEvaluation
public import Structure.ModularCurve_FinitePlaceLift

public noncomputable section

set_option autoImplicit false

noncomputable section

open AlgebraicCurve ResidueField

namespace ModularCurve

section NuBall

variable (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥L]
  (ν : NumberField.FinitePlace ↥L)


public theorem mem_nuBall_iff (a : ↥L) : a ∈ nuBall L ν ↔ ν a ≤ 1 := Iff.rfl


public theorem isUnit_nuBall_iff (a : ↥L) (ha : ν a ≤ 1) :
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


namespace FinitePlaceLift

variable {L : IntermediateField ℚ (AlgebraicClosure ℚ)} [NumberField ↥L]
  {ν : NumberField.FinitePlace ↥L} (M : FinitePlaceLift L ν)


public theorem isUnit_mk_iff (a : ↥L) (hmem : (↑a : AlgebraicClosure ℚ) ∈ M.A) :
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


public theorem mem_maximalIdeal_iff (a : ↥L) (hmem : (↑a : AlgebraicClosure ℚ) ∈ M.A) :
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


public theorem charP_residueField : CharP (IsLocalRing.ResidueField ↥M.A) M.p :=
  ValuationSubring.charP_residueField_of_liesOverPrime_def M.pprime M.lies


public theorem nu_p_lt_one : ν ((M.p : ℕ) : ↥L) < 1 := by
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


public theorem mem_maximalIdeal_nuBall_iff (a : ↥(nuBall L ν)) :
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


@[simp] public theorem traceHom_coe (M : FinitePlaceLift L ν) (a : ↥(nuBall L ν)) :
    ((M.traceHom a : ↥M.A) : AlgebraicClosure ℚ) = ((↑a : ↥L) : AlgebraicClosure ℚ) := rfl


public theorem residueFieldEmb_residue (M : FinitePlaceLift L ν) (a : ↥(nuBall L ν)) :
    M.residueFieldEmb (IsLocalRing.residue _ a) = IsLocalRing.residue ↥M.A (M.traceHom a) :=
  rfl

end FinitePlaceLift

section Existence

variable (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥L]
  (ν : NumberField.FinitePlace ↥L)


public theorem mem_nuBallOpen_iff (a : ↥(nuBall L ν)) : a ∈ nuBallOpen L ν ↔ ν ↑a < 1 := Iff.rfl


public theorem constIncl_injective : Function.Injective (constIncl L) := (constIncl L).injective


public theorem exists_valuationSubring_trace_eq :
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


public theorem exists_prime_nu_lt_one : ∃ q : ℕ, q.Prime ∧ ν ((q : ℕ) : ↥L) < 1 := by
  classical
  obtain ⟨q, n, hn, hqP, hq, -⟩ :=
    Ideal.exists_prime_and_absNorm_eq_pow (NumberField.FinitePlace.maximalIdeal ν).asIdeal
  refine ⟨q, hq, ?_⟩
  have hlt := (NumberField.FinitePlace.norm_lt_one_iff_mem ↥L
    (NumberField.FinitePlace.maximalIdeal ν)
    ((q : ℕ) : NumberField.RingOfIntegers ↥L)).mpr hqP
  rw [NumberField.FinitePlace.norm_embedding_eq, map_natCast] at hlt
  exact hlt


public theorem exists_finitePlaceLift : Nonempty (FinitePlaceLift L ν) := by
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


public theorem nonempty_finitePlaceLift (L : IntermediateField ℚ (AlgebraicClosure ℚ))
    [NumberField ↥L] (ν : NumberField.FinitePlace ↥L) : Nonempty (FinitePlaceLift L ν) :=
  exists_finitePlaceLift L ν

end ModularCurve

namespace AlgebraicCurve

open IsLocalRing

variable {K : Type*} [Field K] {A : ValuationSubring K}
variable {F : Type*} [Field F] [Algebra K F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

namespace ConstantReduction


public theorem maximalIdeal_top_eq_bot (X : Type*) [Field X] :
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


public theorem residueTopEquiv_residue (a : ↥(⊤ : ValuationSubring L)) :
    residueTopEquiv L (IsLocalRing.residue _ a) = (a : L) := rfl


public theorem placeMapOfTop_injective : Function.Injective (placeMapOfTop L F) :=
  fun _ _ h => Place.ext (congrArg
    (fun Q : Place (ResidueField ↥(⊤ : ValuationSubring L)) F => Q.toValuationSubring) h)


public theorem placeMapOfTop_surjective : Function.Surjective (placeMapOfTop L F) := by
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


public theorem ord_placeMapOfTop (P : Place L F) (f : F) :
    (placeMapOfTop L F P).ord f = P.ord f := rfl


public theorem isPointwise_ofTop_of_isEmpty [IsEmpty (Place L F)] : (ofTop L F).IsPointwise :=
  fun P => isEmptyElim P


public theorem isEmpty_place_self : IsEmpty (Place L L) :=
  ⟨fun P => P.ne_top' (by
    ext x
    simp only [ValuationSubring.mem_top, iff_true]
    exact P.algebraMap_mem' x)⟩


public theorem isPointwise_ofTop_self : (ofTop L L).IsPointwise :=
  haveI : IsEmpty (Place L L) := isEmpty_place_self L
  isPointwise_ofTop_of_isEmpty L L


public theorem exists_isDiscParam_ofTop (v : Place L F) :
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


public theorem isPointwise_ofTop (L : Type*) [Field L] (F : Type*) [Field F] [Algebra L F] :
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
