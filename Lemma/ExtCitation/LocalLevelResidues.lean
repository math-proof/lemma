import Mathlib
import Instance.ExtEndgame_ProductionDatum
import Lemma.EllipticCurve.FrobeniusTrace
import Lemma.Deformations.Frobenius
import Abbrev.ExtCitation_LocalLevelResidues

set_option autoImplicit false

open ExtCitation
open scoped NNReal

namespace ExtCitation.LocalLevel

theorem index_op_s17 {G : Type*} [Group G] (H : Subgroup G) :
    H.op.index = H.index := by
  trans (H.comap (MulEquiv.inv' G).symm.toMonoidHom).index
  · congr 1
    ext; simp
  · exact Subgroup.index_comap_of_surjective _ (MulEquiv.inv' G).symm.surjective


lemma totallyBounded_s17 {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (H : ∀ s ∈ nhds (1 : G), ∃ H : Subgroup G, H.FiniteIndex ∧ ↑H ⊆ s) :
    letI := IsTopologicalGroup.rightUniformSpace G
    TotallyBounded (Set.univ : Set G) := by
  letI := IsTopologicalGroup.rightUniformSpace G
  rintro s ⟨t, ht1, hts⟩
  obtain ⟨H, hH, hHs⟩ := H _ ht1
  have : Finite (Gᵐᵒᵖ ⧸ H.op) := Subgroup.finite_quotient_of_finiteIndex
  refine ⟨Set.range (MulOpposite.unop ∘ Quotient.out : Gᵐᵒᵖ ⧸ H.op → G),
    Set.finite_range _, fun x _ ↦
      Set.mem_iUnion₂_of_mem ⟨QuotientGroup.mk (.op x), rfl⟩ (hts (hHs ?_))⟩
  dsimp only
  rw [Function.comp_apply, SetLike.mem_coe, ← MulOpposite.unop_op (x⁻¹),
    ← MulOpposite.unop_mul, ← Subgroup.mem_op, MulOpposite.op_inv, ← QuotientGroup.eq]
  simp


section Local

variable (q : ℕ) [Fact q.Prime]


@[simp] theorem coe_smul_OO (g : GG q) (x : OO q) : ((g • x : OO q) : PadicAlgCl q) = g (x : PadicAlgCl q) := rfl


noncomputable def intToOO : ℤ_[q] →+* OO q :=
  ((algebraMap ℚ_[q] (PadicAlgCl q)).comp PadicInt.Coe.ringHom).codRestrict (padicIntegers q) (fun x => by
    show algebraMap ℚ_[q] (PadicAlgCl q) (x : ℚ_[q]) ∈ padicIntegers q
    rw [mem_padicIntegers_iff, ← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]
    change ‖((x : ℚ_[q]) : PadicAlgCl q)‖ ≤ 1
    rw [PadicAlgCl.norm_extends]
    exact x.2)


theorem algebraMap_OO_coe (x : ℤ_[q]) :
    ((algebraMap ℤ_[q] (OO q) x : OO q) : PadicAlgCl q) = algebraMap ℚ_[q] (PadicAlgCl q) (x : ℚ_[q]) := rfl


theorem natCast_mem_nonunits : ((q : ℕ) : PadicAlgCl q) ∈ (padicIntegers q).nonunits := by
  have hq : Valued.v ((q : ℕ) : PadicAlgCl q) = 1 / (q : ℝ≥0) := PadicAlgCl.valuation_p q
  have hq2 : (2 : ℕ) ≤ q := (Fact.out : q.Prime).two_le
  rw [ValuationSubring.mem_nonunits_iff, ← (Valuation.isEquiv_valuation_valuationSubring _).lt_one_iff_lt_one]
  change Valued.v ((q : ℕ) : PadicAlgCl q) < 1
  rw [hq, div_lt_one (by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_two hq2)]
  exact_mod_cast Nat.lt_of_lt_of_le Nat.one_lt_two hq2

theorem under_maximalIdeal_eq :
    (IsLocalRing.maximalIdeal (OO q)).under ℤ_[q] = IsLocalRing.maximalIdeal ℤ_[q] := by
  set P := (IsLocalRing.maximalIdeal (OO q)).under ℤ_[q] with hPdef
  have hqP : ((q : ℕ) : ℤ_[q]) ∈ P := by
    change ((q : ℕ) : ℤ_[q]) ∈ Ideal.comap (algebraMap ℤ_[q] (OO q)) (IsLocalRing.maximalIdeal (OO q))
    rw [Ideal.mem_comap, ← ValuationSubring.coe_mem_nonunits_iff, map_natCast]
    have : (((q : ℕ) : OO q) : PadicAlgCl q) = ((q : ℕ) : PadicAlgCl q) := by simp
    rw [this]
    exact natCast_mem_nonunits q
  have hP0 : P ≠ ⊥ := fun h => by
    have h0 : ((q : ℕ) : ℤ_[q]) = 0 := by simpa [h] using hqP
    exact (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero) h0
  haveI : P.IsPrime := Ideal.IsPrime.under ℤ_[q] (IsLocalRing.maximalIdeal (OO q))
  exact IsLocalRing.eq_maximalIdeal (Ideal.IsPrime.isMaximal ‹P.IsPrime› hP0)

theorem exists_frob_local : ∃ σ : GG q, ∀ x : OO q,
    ((σ • x - x ^ q : OO q) : PadicAlgCl q) ∈ (padicIntegers q).nonunits := by
  haveI : Algebra.IsIntegral ℚ_[q] (PadicAlgCl q) := ⟨fun x => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral⟩
  let Q := IsLocalRing.maximalIdeal (OO q)
  have hP : Q.under ℤ_[q] = IsLocalRing.maximalIdeal ℤ_[q] := under_maximalIdeal_eq q
  haveI : Finite (ℤ_[q] ⧸ Q.under ℤ_[q]) := by
    rw [hP]
    exact Finite.of_equiv _ (PadicInt.residueField (p := q)).toEquiv.symm
  have hcard : Nat.card (ℤ_[q] ⧸ Q.under ℤ_[q]) = q := by
    rw [Nat.card_congr ((Ideal.quotEquivOfEq hP).toEquiv.trans (PadicInt.residueField (p := q)).toEquiv), Nat.card_zmod]
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant_of_profinite ℤ_[q] (GG q) Q
  refine ⟨σ, fun x => ?_⟩
  have hx := hσ x
  rw [hcard] at hx
  exact ValuationSubring.coe_mem_nonunits_iff.mpr hx

end Local

theorem mem_nonunits_comap {K L : Type*} [Field K] [Field L] {B : ValuationSubring L} {f : K →+* L} {x : K} :
    x ∈ (B.comap f).nonunits ↔ f x ∈ B.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_comap, map_inv₀]
  constructor
  · rintro (rfl | h)
    · exact Or.inl (map_zero f)
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl ((map_eq_zero f).mp h)
    · exact Or.inr h

theorem mem_nonunits_padicPlace_iff (q : ℕ) [Fact q.Prime] {x : AlgebraicClosure ℚ} :
    x ∈ (padicPlace q).nonunits ↔ padicEmbedding q x ∈ (padicIntegers q).nonunits := by
  rw [padicPlace, mem_nonunits_comap]
  rfl

theorem coe_decomp_smul {K L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring L)
    (d : A.decompositionSubgroup K) (a : A) : ((d • a : A) : L) = (d : L ≃ₐ[K] L) a := rfl

section LevelW

variable (q : ℕ) [Fact q.Prime]
variable (Kw : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] Kw]

noncomputable def RwToOO : Rw q Kw →+* OO q :=
  ((algebraMap Kw (PadicAlgCl q)).comp (Rw q Kw).subtype).codRestrict (padicIntegers q) (fun x => x.2)


theorem algebraMap_Rw_coe (x : Rw q Kw) :
    ((algebraMap (Rw q Kw) (OO q) x : OO q) : PadicAlgCl q) = ((x : Kw) : PadicAlgCl q) := rfl


theorem stabilizerHom_surjective_Gw :
    Function.Surjective (Ideal.Quotient.stabilizerHom (IsLocalRing.maximalIdeal (OO q))
      ((IsLocalRing.maximalIdeal (OO q)).under (Rw q Kw)) (Gw q Kw)) := by
  haveI : Algebra.IsIntegral ℚ_[q] (PadicAlgCl q) := ⟨fun x => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral⟩
  letI : TopologicalSpace (OO q) := ⊥
  haveI : DiscreteTopology (OO q) := ⟨rfl⟩
  exact Ideal.Quotient.stabilizerHom_surjective_of_profinite (G := Gw q Kw)
    ((IsLocalRing.maximalIdeal (OO q)).under (Rw q Kw)) (IsLocalRing.maximalIdeal (OO q))

end LevelW

section Residues

variable (q : ℕ) [Fact q.Prime]

theorem natCast_residue_eq_zero : ((q : ℕ) : kbar q) = 0 := by
  rw [← map_natCast (IsLocalRing.residue (OO q)), IsLocalRing.residue_eq_zero_iff]
  rw [← ValuationSubring.coe_mem_nonunits_iff]
  have : (((q : ℕ) : OO q) : PadicAlgCl q) = ((q : ℕ) : PadicAlgCl q) := by simp
  rw [this]
  exact natCast_mem_nonunits q


theorem algebraMap_toZMod (z : ℤ_[q]) :
    algebraMap (ZMod q) (kbar q) (PadicInt.toZMod z) = IsLocalRing.residue (OO q) (algebraMap ℤ_[q] (OO q) z) := by
  have hspec := PadicInt.toZMod_spec z
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hspec
  obtain ⟨w, hw⟩ := hspec
  have hz : z = (ZMod.cast (PadicInt.toZMod z) : ℤ_[q]) + (q : ℤ_[q]) * w := by rw [← hw]; ring
  conv_rhs => rw [hz]
  rw [map_add, map_add, map_mul, map_mul, map_natCast, map_natCast, natCast_residue_eq_zero, zero_mul, add_zero,
    ZMod.cast_eq_val, map_natCast, map_natCast]
  change ZMod.cast (PadicInt.toZMod z) = ((PadicInt.toZMod z).val : kbar q)
  rw [ZMod.cast_eq_val]

noncomputable def kM (M : ℕ) : IntermediateField (ZMod q) (kbar q) where
  carrier := {y | y ^ (q ^ M) = y}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [mul_pow, ha, hb]
  one_mem' := by simp only [Set.mem_setOf_eq, one_pow]
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [add_pow_char_pow, ha, hb]
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    exact zero_pow (pow_ne_zero _ (Fact.out : q.Prime).ne_zero)
  algebraMap_mem' a := by
    simp only [Set.mem_setOf_eq]
    rw [← map_pow, ZMod.pow_card_pow]
  inv_mem' a ha := by
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [inv_pow, ha]

theorem mem_kM_iff {M : ℕ} {y : kbar q} : y ∈ kM q M ↔ y ^ (q ^ M) = y := Iff.rfl

theorem finite_kM (M : ℕ) (hM : 0 < M) : Finite (kM q M) := by
  classical
  have h1 : 1 < q ^ M := Nat.one_lt_pow hM.ne' (Fact.out : q.Prime).one_lt
  · have hne : (Polynomial.X ^ (q ^ M) - Polynomial.X : Polynomial (kbar q)) ≠ 0 :=
      FiniteField.X_pow_card_sub_X_ne_zero (kbar q) h1
    have hsub : ((kM q M) : Set (kbar q)) ⊆ ((Polynomial.X ^ (q ^ M) - Polynomial.X : Polynomial (kbar q)).roots.toFinset : Set (kbar q)) := by
      intro y hy
      rw [SetLike.mem_coe, mem_kM_iff] at hy
      simp only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hne, Polynomial.IsRoot.def,
        Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, hy, sub_self]
    exact Set.Finite.to_subtype (Set.Finite.subset (Finset.finite_toSet _) hsub)

noncomputable def resAut (M : ℕ) (g : GG q) : (kM q M) ≃ₐ[ZMod q] (kM q M) where
  toFun y := ⟨g • (y : kbar q), by
    have hy := y.2; rw [mem_kM_iff] at hy ⊢; rw [← smul_pow', hy]⟩
  invFun y := ⟨g⁻¹ • (y : kbar q), by
    have hy := y.2; rw [mem_kM_iff] at hy ⊢; rw [← smul_pow', hy]⟩
  left_inv y := Subtype.ext (inv_smul_smul g (y : kbar q))
  right_inv y := Subtype.ext (smul_inv_smul g (y : kbar q))
  map_mul' a b := Subtype.ext (smul_mul' g (a : kbar q) (b : kbar q))
  map_add' a b := Subtype.ext (smul_add g (a : kbar q) (b : kbar q))
  commutes' a := Subtype.ext (by
    change g • (algebraMap (ZMod q) (kbar q) a) = algebraMap (ZMod q) (kbar q) a
    have : algebraMap (ZMod q) (kbar q) a = ((a.val : ℕ) : kbar q) := by
      change ZMod.cast a = _; rw [ZMod.cast_eq_val]
    rw [this]
    exact map_natCast (MulSemiringAction.toRingHom (GG q) (kbar q) g) a.val)

theorem coe_resAut (M : ℕ) (g : GG q) (y : kM q M) : ((resAut q M g y : kM q M) : kbar q) = g • (y : kbar q) := rfl

theorem exists_smul_eq_pow (M : ℕ) (hM : 0 < M) (g : GG q) :
    ∃ n : ℕ, ∀ y : kbar q, y ∈ kM q M → g • y = y ^ (q ^ n) := by
  haveI : Finite (kM q M) := finite_kM q M hM
  haveI : Algebra.IsAlgebraic (ZMod q) (kM q M) := Algebra.IsAlgebraic.of_finite (ZMod q) (kM q M)
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod q) (kM q M)).2 (resAut q M g)
  refine ⟨n, fun y hy => ?_⟩
  have := congrArg (fun e : (kM q M) ≃ₐ[ZMod q] (kM q M) => ((e ⟨y, hy⟩ : kM q M) : kbar q)) hn
  simp only [coe_resAut] at this
  rw [← this, AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate, ZMod.card]
  rfl

theorem pow_pow_mul_eq {R : Type*} [Monoid R] {x : R} {a : ℕ} (h : x ^ (q ^ a) = x) (b : ℕ) : x ^ (q ^ (a * b)) = x := by
  induction b with
  | zero => simp
  | succ b ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, h]

end Residues

section DegreeBound

variable (q : ℕ) [Fact q.Prime]
variable (Kw : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] Kw]

theorem exists_monic_lift (x : Kw) (hx : x ∈ Rw q Kw) :
    ∃ P : Polynomial ℤ_[q], P.Monic ∧ P.map PadicInt.Coe.ringHom = minpoly ℚ_[q] x := by
  have hint : IsIntegral ℚ_[q] x := IsIntegral.of_finite ℚ_[q] x
  have hx1 : spectralNorm ℚ_[q] (PadicAlgCl q) (x : PadicAlgCl q) ≤ 1 := by
    have : ‖(x : PadicAlgCl q)‖₊ ≤ 1 := (mem_padicIntegers_iff q).mp hx
    have h' : ‖(x : PadicAlgCl q)‖ ≤ 1 := by exact_mod_cast this
    exact h'
  have hmin : minpoly ℚ_[q] (x : PadicAlgCl q) = minpoly ℚ_[q] x :=
    minpoly.algebraMap_eq (algebraMap Kw (PadicAlgCl q)).injective x
  have hlifts : minpoly ℚ_[q] x ∈ Polynomial.lifts (PadicInt.Coe.ringHom (p := q)) := by
    refine (Polynomial.lifts_iff_coeff_lifts _).mpr fun i => ?_
    have hci : ‖(minpoly ℚ_[q] x).coeff i‖ ≤ 1 := by
      rw [← hmin]
      have := (ciSup_le_iff (spectralValueTerms_bddAbove (minpoly ℚ_[q] (x : PadicAlgCl q)))).mp hx1 i
      simp only [spectralValueTerms] at this
      split_ifs at this with h
      · conv_rhs at this => rw [← Real.one_rpow (1 / (↑(minpoly ℚ_[q] (x : PadicAlgCl q)).natDegree - ↑i) : ℝ)]
        rw [Real.rpow_le_rpow_iff (by positivity) (by positivity) (by
          rw [one_div_pos, sub_pos]; exact_mod_cast h)] at this
        exact this
      · obtain h | h := (le_of_not_gt h).eq_or_lt
        · have hmon' : (minpoly ℚ_[q] (x : PadicAlgCl q)).Monic := by rw [hmin]; exact minpoly.monic hint
          rw [← h, hmon'.coeff_natDegree, norm_one]
        · rw [Polynomial.coeff_eq_zero_of_natDegree_lt h, norm_zero]; exact zero_le_one
    exact ⟨⟨_, hci⟩, rfl⟩
  obtain ⟨P, hP, -, hmon⟩ := Polynomial.lifts_and_degree_eq_and_monic hlifts (minpoly.monic hint)
  exact ⟨P, hmon, hP⟩

theorem residue_mem_kM (x : Rw q Kw) :
    IsLocalRing.residue (OO q) (algebraMap (Rw q Kw) (OO q) x) ∈ kM q (Module.finrank ℚ_[q] Kw).factorial := by
  classical
  obtain ⟨P, hmon, hP⟩ := exists_monic_lift q Kw (x : Kw) x.2
  set X : OO q := algebraMap (Rw q Kw) (OO q) x with hXdef
  set xb : kbar q := IsLocalRing.residue (OO q) X with hxbdef

  have h1 : Polynomial.eval₂ (algebraMap ℤ_[q] (OO q)) X P = 0 := by
    apply Subtype.val_injective
    rw [show ((Polynomial.eval₂ (algebraMap ℤ_[q] (OO q)) X P : OO q) : PadicAlgCl q)
        = Polynomial.eval₂ ((padicIntegers q).subtype.comp (algebraMap ℤ_[q] (OO q))) (X : PadicAlgCl q) P from
        Polynomial.hom_eval₂ P (algebraMap ℤ_[q] (OO q)) (padicIntegers q).subtype X]
    have hcomp : (padicIntegers q).subtype.comp (algebraMap ℤ_[q] (OO q))
        = (algebraMap ℚ_[q] (PadicAlgCl q)).comp PadicInt.Coe.ringHom := by
      ext z; rfl
    rw [hcomp, ← Polynomial.eval₂_map, hP, ZeroMemClass.coe_zero]
    change Polynomial.eval₂ (algebraMap ℚ_[q] (PadicAlgCl q)) (algebraMap Kw (PadicAlgCl q) (x : Kw)) (minpoly ℚ_[q] (x : Kw)) = 0
    rw [← Polynomial.aeval_def, Polynomial.aeval_algebraMap_apply, minpoly.aeval, map_zero]

  set Pb : Polynomial (ZMod q) := P.map (PadicInt.toZMod (p := q)) with hPbdef
  have h2 : Polynomial.aeval xb Pb = 0 := by
    rw [Polynomial.aeval_def, hPbdef, Polynomial.eval₂_map]
    have hcomp : (algebraMap (ZMod q) (kbar q)).comp (PadicInt.toZMod (p := q))
        = (IsLocalRing.residue (OO q)).comp (algebraMap ℤ_[q] (OO q)) := by
      ext z; exact algebraMap_toZMod q z
    rw [hcomp, hxbdef, ← Polynomial.hom_eval₂, h1, map_zero]
  have hPbmon : Pb.Monic := hmon.map _
  have hPbdeg : Pb.natDegree ≤ Module.finrank ℚ_[q] Kw := by
    rw [hPbdef, hmon.natDegree_map]
    have : P.natDegree = (minpoly ℚ_[q] (x : Kw)).natDegree := by rw [← hP, hmon.natDegree_map]
    rw [this]
    exact minpoly.natDegree_le (x : Kw)

  have hxbint : IsIntegral (ZMod q) xb := ⟨Pb, hPbmon, h2⟩
  let E := IntermediateField.adjoin (ZMod q) ({xb} : Set (kbar q))
  haveI : FiniteDimensional (ZMod q) E := IntermediateField.adjoin.finiteDimensional hxbint
  have hd : Module.finrank (ZMod q) E ≤ Module.finrank ℚ_[q] Kw := by
    rw [IntermediateField.adjoin.finrank hxbint]
    exact (Polynomial.natDegree_le_natDegree (minpoly.min (ZMod q) xb hPbmon h2)).trans hPbdeg
  have hdpos : 0 < Module.finrank (ZMod q) E := Module.finrank_pos
  haveI : Finite E := Module.finite_of_finite (ZMod q)
  letI : Fintype E := Fintype.ofFinite E
  have hcard : Fintype.card E = q ^ Module.finrank (ZMod q) E := by
    rw [Module.card_eq_pow_finrank (K := ZMod q) (V := E), ZMod.card]
  have hfermat : xb ^ (q ^ Module.finrank (ZMod q) E) = xb := by
    have := FiniteField.pow_card (⟨xb, IntermediateField.mem_adjoin_simple_self (ZMod q) xb⟩ : E)
    rw [hcard] at this
    exact congrArg Subtype.val this

  rw [mem_kM_iff]
  obtain ⟨c, hc⟩ := Nat.dvd_factorial hdpos hd
  rw [hc]
  exact pow_pow_mul_eq q hfermat c

end DegreeBound

section Transport

variable (q : ℕ) [Fact q.Prime]

theorem rD_smul_residue_eq_pow (w : GG q) (e : ℕ)
    (hw : ∀ x : OO q, ((w • x - x ^ e : OO q) : PadicAlgCl q) ∈ (padicIntegers q).nonunits)
    (a : ↥(padicPlace q)) :
    rD q w • IsLocalRing.residue _ a = (IsLocalRing.residue _ a) ^ e := by
  rw [← map_pow, ← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
    ← ValuationSubring.coe_mem_nonunits_iff, mem_nonunits_padicPlace_iff]
  let x : OO q := ⟨padicEmbedding q (a : AlgebraicClosure ℚ), a.2⟩
  have key := hw x
  have hcoe : padicEmbedding q (((rD q w • a - a ^ e : ↥(padicPlace q))) : AlgebraicClosure ℚ)
      = ((w • x - x ^ e : OO q) : PadicAlgCl q) := by
    simp only [AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow, map_sub, map_pow, coe_decomp_smul, coe_smul_OO,
      MonoidHom.codRestrict_apply, padicEmbedding_localGaloisToGlobal, x]
  rw [hcoe]
  exact key

theorem isFrobeniusAt_of_local (σ : GG q)
    (hσ : ∀ x : OO q, ((σ • x - x ^ q : OO q) : PadicAlgCl q) ∈ (padicIntegers q).nonunits) :
    (padicPlace q).IsFrobeniusAt (localGaloisToGlobal q σ) q :=
  ⟨localGaloisToGlobal_mem_decompositionSubgroup q σ, fun y => by
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
    exact rD_smul_residue_eq_pow q σ q hσ a⟩

theorem rD_pow_smul (ψ : GG q) (hψ : (padicPlace q).IsFrobeniusAt (localGaloisToGlobal q ψ) q)
    (k : ℕ) (y : IsLocalRing.ResidueField ↥(padicPlace q)) : rD q (ψ ^ k) • y = y ^ (q ^ k) := by
  induction k generalizing y with
  | zero => rw [pow_zero, map_one, one_smul, pow_zero, pow_one]
  | succ k ih =>
    rw [pow_succ, map_mul, mul_smul, (show rD q ψ • y = y ^ q from hψ.smul_residue_eq y), smul_pow', ih, ← pow_mul, ← pow_succ]

theorem mem_inertiaPullback_iff_nat (g : GG q) :
    g ∈ ((padicPlace q).inertiaSubgroupIn ℚ).comap (localGaloisToGlobal q) ↔
      ∀ x : IsLocalRing.ResidueField ↥(padicPlace q), rD q g • x = x := by
  rw [Subgroup.mem_comap, ValuationSubring.inertiaSubgroupIn, Subgroup.mem_map]
  constructor
  · rintro ⟨τ, hτ, hτg⟩
    intro x
    have hmem : rD q g = τ := by
      apply Subtype.ext; exact hτg.symm
    rw [hmem]
    rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker] at hτ
    have := congrArg (fun φ => (φ : IsLocalRing.ResidueField ↥(padicPlace q) ≃+* _) x) hτ
    simpa using this
  · intro h
    refine ⟨rD q g, ?_, rfl⟩
    rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker]
    apply RingEquiv.ext
    intro x
    simpa using h x

theorem pow_smul_kbar (φ₀ : GG q) (hφ₀res : ∀ z : kbar q, φ₀ • z = z ^ q) (k : ℕ) (z : kbar q) :
    (φ₀ ^ k) • z = z ^ (q ^ k) := by
  induction k generalizing z with
  | zero => rw [pow_zero, one_smul, pow_zero, pow_one]
  | succ k ih => rw [pow_succ, mul_smul, hφ₀res, smul_pow', ih, ← pow_mul, ← pow_succ]

end Transport

section ResidueMap

variable (q : ℕ) [Fact q.Prime] (Kw : IntermediateField ℚ_[q] (PadicAlgCl q))

theorem resw_def (x : Rw q Kw) : resw q Kw x = IsLocalRing.residue (OO q) (algebraMap (Rw q Kw) (OO q) x) := rfl

end ResidueMap

section Commute

variable (q : ℕ) [Fact q.Prime]

theorem exists_mem_kM (z : kbar q) : ∃ M : ℕ, 0 < M ∧ z ∈ kM q M := by
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z

  have hxint : IsIntegral ℚ_[q] (x : PadicAlgCl q) := (Algebra.IsAlgebraic.isAlgebraic (x : PadicAlgCl q)).isIntegral
  let Kw : IntermediateField ℚ_[q] (PadicAlgCl q) := IntermediateField.adjoin ℚ_[q] {(x : PadicAlgCl q)}
  haveI : FiniteDimensional ℚ_[q] Kw := IntermediateField.adjoin.finiteDimensional hxint
  have hxK : (x : PadicAlgCl q) ∈ Kw := IntermediateField.mem_adjoin_simple_self ℚ_[q] _
  let xr : Rw q Kw := ⟨⟨(x : PadicAlgCl q), hxK⟩, show algebraMap Kw (PadicAlgCl q) ⟨(x : PadicAlgCl q), hxK⟩ ∈ padicIntegers q from x.2⟩
  refine ⟨(Module.finrank ℚ_[q] Kw).factorial, Nat.factorial_pos _, ?_⟩
  have := residue_mem_kM q Kw xr
  convert this using 2
  exact Subtype.ext rfl

theorem smul_smul_comm_kbar (g h : GG q) (z : kbar q) : g • (h • z) = h • (g • z) := by
  obtain ⟨M, hM, hz⟩ := exists_mem_kM q z
  obtain ⟨a, ha⟩ := exists_smul_eq_pow q M hM g
  obtain ⟨b, hb⟩ := exists_smul_eq_pow q M hM h
  have hzg : g • z ∈ kM q M := by rw [mem_kM_iff] at hz ⊢; rw [← smul_pow', hz]
  have hzh : h • z ∈ kM q M := by rw [mem_kM_iff] at hz ⊢; rw [← smul_pow', hz]
  rw [ha _ hzh, hb _ hz, hb _ hzg, ha _ hz, ← pow_mul, ← pow_mul, mul_comm]

theorem commutator_smul_sub_mem (g h : GG q) (x : OO q) :
    (((g * h * g⁻¹ * h⁻¹) • x - x ^ 1 : OO q) : PadicAlgCl q) ∈ (padicIntegers q).nonunits := by
  rw [ValuationSubring.coe_mem_nonunits_iff, ← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero, pow_one,
    IsLocalRing.ResidueField.residue_smul]
  set z := IsLocalRing.residue (OO q) x
  rw [mul_smul, mul_smul, mul_smul, smul_smul_comm_kbar q g⁻¹ h⁻¹ z, smul_inv_smul, smul_inv_smul]

end Commute

section MoveLikeFrobenius

variable (q : ℕ) [Fact q.Prime]

theorem mem_inertiaPullback_of_smul_sub_mem (w : GG q)
    (hw : ∀ x : OO q, ((w • x - x ^ 1 : OO q) : PadicAlgCl q) ∈ (padicIntegers q).nonunits) :
    w ∈ ((padicPlace q).inertiaSubgroupIn ℚ).comap (localGaloisToGlobal q) := by
  refine (mem_inertiaPullback_iff_nat q w).mpr fun y => ?_
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
  rw [rD_smul_residue_eq_pow q _ 1 hw a, pow_one]

variable (Kw : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] Kw]

theorem apply_eq_of_trivial_on_residues (h : GG q)
    (hh : ∀ x : Rw q Kw, h • IsLocalRing.residue (OO q) (algebraMap (Rw q Kw) (OO q) x)
      = IsLocalRing.residue (OO q) (algebraMap (Rw q Kw) (OO q) x))
    (y : PadicAlgCl q) (hy : y ∈ Kw)
    (hI : ∀ w : GG q, (∀ x : OO q, ((w • x - x ^ 1 : OO q) : PadicAlgCl q) ∈ (padicIntegers q).nonunits) → w y = y) :
    h y = y := by
  classical
  let Q := IsLocalRing.maximalIdeal (OO q)
  let σbar : (OO q ⧸ Q) ≃ₐ[Rw q Kw ⧸ Q.under (Rw q Kw)] (OO q ⧸ Q) :=
    { MulSemiringAction.toRingEquiv (GG q) (kbar q) h with
      commutes' := fun r => by
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
        exact hh r }
  obtain ⟨u, hu⟩ := stabilizerHom_surjective_Gw q Kw σbar
  set uG : GG q := ((u : Gw q Kw) : GG q) with huGdef
  have hu' : ∀ bb : OO q, IsLocalRing.residue (OO q) (uG • bb) = h • IsLocalRing.residue (OO q) bb := by
    intro bb
    exact congrArg (fun e => e (Ideal.Quotient.mk Q bb)) hu

  have hw : ∀ x : OO q, (((h⁻¹ * uG) • x - x ^ 1 : OO q) : PadicAlgCl q) ∈ (padicIntegers q).nonunits := by
    intro x
    rw [ValuationSubring.coe_mem_nonunits_iff, ← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero, pow_one,
      IsLocalRing.ResidueField.residue_smul, mul_smul, ← IsLocalRing.ResidueField.residue_smul, hu', inv_smul_smul]
  have hwy : (h⁻¹ * uG) y = y := hI _ hw
  have huy : uG y = y := (IntermediateField.mem_fixingSubgroup_iff Kw uG).mp u.1.2 y hy

  have : h = uG * (h⁻¹ * uG)⁻¹ := by group
  rw [this, AlgEquiv.mul_apply]
  have hw' : (h⁻¹ * uG)⁻¹ y = y := by
    rw [AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq]; exact hwy.symm
  rw [hw', huy]

theorem exists_apply_eq_frob_pow_apply (φ₀ : GG q) (hφ₀res : ∀ z : kbar q, φ₀ • z = z ^ q)
    (y : PadicAlgCl q) (hy : y ∈ Kw)
    (hI : ∀ w : GG q, (∀ x : OO q, ((w • x - x ^ 1 : OO q) : PadicAlgCl q) ∈ (padicIntegers q).nonunits) → w y = y)
    (g : GG q) : ∃ j : ℕ, g y = (φ₀ ^ j) y := by
  set N : ℕ := Module.finrank ℚ_[q] Kw with hNdef
  obtain ⟨n, hn⟩ := exists_smul_eq_pow q N.factorial (Nat.factorial_pos N) g
  refine ⟨n, ?_⟩
  have hφ₀n : ∀ z : kbar q, (φ₀ ^ n) • z = z ^ (q ^ n) := pow_smul_kbar q φ₀ hφ₀res n
  have hh : ∀ x : Rw q Kw,
      ((φ₀ ^ n)⁻¹ * g) • IsLocalRing.residue (OO q) (algebraMap (Rw q Kw) (OO q) x)
        = IsLocalRing.residue (OO q) (algebraMap (Rw q Kw) (OO q) x) := by
    intro x
    have hx := hn _ (residue_mem_kM q Kw x)
    rw [mul_smul, hx, ← hφ₀n, inv_smul_smul]
  have := apply_eq_of_trivial_on_residues q Kw ((φ₀ ^ n)⁻¹ * g) hh y hy hI
  rw [AlgEquiv.mul_apply] at this

  rw [AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq] at this
  exact this

theorem frob_pow_apply_eq (φ₀ : GG q) (j : ℕ)
    (hj : ∀ x : Rw q Kw, (φ₀ ^ j) • IsLocalRing.residue (OO q) (algebraMap (Rw q Kw) (OO q) x)
      = IsLocalRing.residue (OO q) (algebraMap (Rw q Kw) (OO q) x))
    (y : PadicAlgCl q) (hy : y ∈ Kw)
    (hI : ∀ w : GG q, (∀ x : OO q, ((w • x - x ^ 1 : OO q) : PadicAlgCl q) ∈ (padicIntegers q).nonunits) → w y = y) :
    (φ₀ ^ j) y = y :=
  apply_eq_of_trivial_on_residues q Kw (φ₀ ^ j) hj y hy hI

end MoveLikeFrobenius

end ExtCitation.LocalLevel
