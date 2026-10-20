import Mathlib
import sympy.Basic
open IntermediateField Polynomial
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false


private noncomputable def frobeniusSubfield (M : Type*) [Field M] (p : ℕ) [ExpChar M p] : Subfield M :=
  (frobenius M p).fieldRange
private lemma mem_frobeniusSubfield_iff {M : Type*} [Field M] (p : ℕ) [ExpChar M p] {a : M} :
  a ∈ frobeniusSubfield M p ↔ ∃ b : M, b ^ p = a := by
  simp [frobeniusSubfield, RingHom.mem_fieldRange, frobenius_def]
private lemma pow_mem_frobeniusSubfield {M : Type*} [Field M] (p : ℕ) [ExpChar M p] (a : M) :
  a ^ p ∈ frobeniusSubfield M p := (mem_frobeniusSubfield_iff p).mpr ⟨a, rfl⟩
private noncomputable def frobeniusRingEquivRange (M : Type*) [Field M] (p : ℕ) [ExpChar M p] :
  M ≃+* frobeniusSubfield M p :=
  RingEquiv.ofBijective (frobenius M p).rangeRestrict
    ⟨fun _ _ h => (frobenius M p).injective (Subtype.ext_iff.mp h),
      (frobenius M p).rangeRestrict_surjective⟩
private lemma frobeniusRingEquivRange_apply
  (M : Type*) [Field M] (p : ℕ) [ExpChar M p]
  (a : M) : ((frobeniusRingEquivRange M p a : frobeniusSubfield M p) : M) = a ^ p := rfl
section Transport
variable {E M : Type*} [Field E] [Field M] [Algebra E M] (p : ℕ) [ExpChar E p]
private noncomputable abbrev frobeniusSubfieldImageInM : Subfield M :=
  (frobeniusSubfield E p).map (algebraMap E M)
private lemma frobeniusSubfieldImageInM_le_algebraMapRange :
  frobeniusSubfieldImageInM (E := E) (M := M) p ≤ (algebraMap E M).fieldRange :=
  fun _ ⟨a, _, ha⟩ => ⟨a, ha⟩
private lemma frobeniusSubfieldImageInM_le_frobeniusSubfield [ExpChar M p] :
  frobeniusSubfieldImageInM (E := E) (M := M) p ≤ frobeniusSubfield M p := by
  rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
  exact ⟨algebraMap E M b, by simp [frobenius_def, map_pow]⟩
private lemma comap_frobenius_frobeniusSubfield [ExpChar M p] :
  (frobeniusSubfield M p).comap (frobenius M p) = ⊤ := by
  ext x; constructor
  ·
    intro _
    trivial
  ·
    intro _
    exact ⟨x, rfl⟩
private lemma comap_frobenius_frobeniusSubfieldImageInM [ExpChar M p] :
  (frobeniusSubfieldImageInM (E := E) (M := M) p).comap (frobenius M p) =
      (algebraMap E M).fieldRange := by
  ext x; constructor
  ·
    rintro ⟨_, ⟨b, rfl⟩, hb⟩
    exact ⟨b, (frobenius M p).injective (by simpa [frobenius_def, map_pow] using hb)⟩
  ·
    rintro ⟨e, rfl⟩
    exact ⟨e ^ p, ⟨e, rfl⟩, by simp [frobenius_def, map_pow]⟩
private lemma finrank_algebraMapRange_eq :
  Module.finrank (↥(algebraMap E M).fieldRange) M = Module.finrank E M := by
  have h := lift_rank_eq_of_equiv_equiv (M := M) (M' := M)
    (R := E) (R' := ↥(algebraMap E M).fieldRange)
    (fun e => (algebraMap E M).rangeRestrictFieldEquiv e) (AddEquiv.refl M)
    (algebraMap E M).rangeRestrictFieldEquiv.bijective
    (fun e m => by
      show e • m = ((algebraMap E M).rangeRestrictFieldEquiv e) • m
      rw [Algebra.smul_def, Subfield.smul_def]
      rfl)
  simp at h
  exact congrArg Cardinal.toNat h.symm
private lemma finrank_frobeniusSubfield_eq
  [ExpChar M p] [FiniteDimensional E M]
  [FiniteDimensional (frobeniusSubfield E p) E] :
  Module.finrank (frobeniusSubfield M p) M = Module.finrank (frobeniusSubfield E p) E := by
  set Mp : Subfield M := frobeniusSubfield M p with hMp
  set Ep' : Subfield M := frobeniusSubfieldImageInM (E := E) (M := M) p with hEp'
  set E' : Subfield M := (algebraMap E M).fieldRange with hE'
  have hfrob : Subfield.relfinrank Ep' Mp = Subfield.relfinrank E' (⊤ : Subfield M) := by
    have h1 := Subfield.relfinrank_comap_comap_eq_relfinrank_of_le (A := Ep') (B := Mp)
      (frobenius M p) (by rw [hMp]; exact le_refl _)
    rw [comap_frobenius_frobeniusSubfield, comap_frobenius_frobeniusSubfieldImageInM] at h1
    apply h1.symm
  have htowerE : Subfield.relfinrank Ep' E' * Subfield.relfinrank E' (⊤ : Subfield M) =
      Subfield.relfinrank Ep' (⊤ : Subfield M) :=
    Subfield.relfinrank_mul_relfinrank
      (frobeniusSubfieldImageInM_le_algebraMapRange p) le_top
  have htowerM : Subfield.relfinrank Ep' Mp * Subfield.relfinrank Mp (⊤ : Subfield M) =
      Subfield.relfinrank Ep' (⊤ : Subfield M) :=
    Subfield.relfinrank_mul_relfinrank
      (frobeniusSubfieldImageInM_le_frobeniusSubfield p) le_top
  have hEp'E' : Subfield.relfinrank Ep' E' = Module.finrank (frobeniusSubfield E p) E := by
    have h1 : E' = (⊤ : Subfield E).map (algebraMap E M) := by
      rw [hE', ← RingHom.fieldRange_eq_map]
    rw [hEp', h1, Subfield.relfinrank_map_map, Subfield.relfinrank_top_right]
  have hMpTop : Subfield.relfinrank Mp (⊤ : Subfield M) = Module.finrank (frobeniusSubfield M p) M :=
    Subfield.relfinrank_top_right _
  have hE'pos : 0 < Subfield.relfinrank E' (⊤ : Subfield M) := by
    rw [Subfield.relfinrank_top_right, hE', finrank_algebraMapRange_eq (E := E) (M := M)]
    apply Module.finrank_pos
  have hcancel : Subfield.relfinrank Ep' E' = Subfield.relfinrank Mp (⊤ : Subfield M) := by
    have h := htowerE.trans htowerM.symm
    rw [hfrob, mul_comm (Subfield.relfinrank E' _)] at h
    exact Nat.eq_of_mul_eq_mul_right hE'pos h
  rw [← hMpTop, ← hcancel, hEp'E']

end Transport

section LinearIndependence
variable {M : Type*} [Field M] (p : ℕ) [hp : Fact p.Prime] [CharP M p] [ExpChar M p]
private lemma pDigits_linearIndependent
  {t : M} (htp : ∀ a : M, a ^ p ≠ t) :
  LinearIndependent (frobeniusSubfield M p)
    (fun i : Fin p => (t ^ (i : ℕ) : M)) := by
  let _ : ExpChar M p := ExpChar.prime hp.out
  have htp' : ∀ c : frobeniusSubfield M p, c ^ p ≠
      (⟨t ^ p, pow_mem_frobeniusSubfield p t⟩ : frobeniusSubfield M p) := by
    rintro ⟨_, b, rfl⟩ hcp
    refine htp b ((frobenius M p).injective ?_)
    have hcp' := congrArg (fun z : frobeniusSubfield M p => (z : M)) hcp
    push_cast at hcp'
    simpa [frobenius_def] using hcp'
  have hirr : Irreducible (X ^ p - C (⟨t ^ p, pow_mem_frobeniusSubfield p t⟩ :
      frobeniusSubfield M p)) :=
    X_pow_sub_C_irreducible_of_prime hp.out htp'
  have hroot : (aeval (R := ↥(frobeniusSubfield M p)) t)
    (X ^ p - C (⟨t ^ p, pow_mem_frobeniusSubfield p t⟩ : frobeniusSubfield M p)) = 0 := by
    simp [map_sub, map_pow, aeval_X, aeval_C]
    exact sub_self _
  have hmon : (X ^ p - C (⟨t ^ p, pow_mem_frobeniusSubfield p t⟩ :
      frobeniusSubfield M p)).Monic := monic_X_pow_sub_C _ hp.out.ne_zero
  have hmp : X ^ p - C (⟨t ^ p, pow_mem_frobeniusSubfield p t⟩ : frobeniusSubfield M p) =
      minpoly (↥(frobeniusSubfield M p)) t :=
    minpoly.eq_of_irreducible_of_monic hirr hroot hmon
  have hdeg : (minpoly (↥(frobeniusSubfield M p)) t).natDegree = p := by
    rw [← hmp, natDegree_X_pow_sub_C]
  have hli := linearIndependent_pow (K := ↥(frobeniusSubfield M p)) t
  rwa [hdeg] at hli

end LinearIndependence

section AdjoinIndex
open scoped IntermediateField
variable {K M : Type*} [Field K] [Field M] [Algebra K M]
  (p : ℕ) [hp : Fact p.Prime] [CharP K p]
private noncomputable abbrev genT (t : M) : ↥K⟮t⟯ := IntermediateField.AdjoinSimple.gen K t
private lemma genT_not_pow (t : M) (htr : Transcendental K t) (a : ↥K⟮t⟯) :
  a ^ p ≠ genT t := by
  intro ha
  have ht0 : t ≠ 0 := fun h => htr (h ▸ isAlgebraic_zero)
  have ha' : t = (↑a : M) ^ p := by
    have := congrArg (fun z : ↥K⟮t⟯ => (z : M)) ha
    push_cast at this; simpa using this.symm
  obtain ⟨r, s, hrs⟩ := (IntermediateField.mem_adjoin_simple_iff K _).mp a.2
  have hkey : aeval t (X * s ^ p - r ^ p) = 0 := by
    simp [map_sub, map_mul, aeval_X, map_pow]
    rw [hrs, div_pow] at ha'
    if hs0 : aeval t s = 0 then
      rw [hs0, zero_pow hp.out.ne_zero, div_zero] at ha'
      exact absurd ha' ht0
    else
      rw [eq_div_iff (pow_ne_zero _ hs0)] at ha'
      rw [sub_eq_zero]
      apply ha'
  have hinj : X * s ^ p - r ^ p = (0 : K[X]) := by
    have := htr
    rw [Transcendental, isAlgebraic_iff_not_injective, not_not] at this
    exact this (by simpa using hkey)
  have hs0 : s ≠ 0 := by
    intro h0; rw [h0] at hrs
    simp [map_zero, div_zero] at hrs
    refine ht0 (ha'.trans ?_)
    rw [hrs]
    simp
    apply hp.out.ne_zero
  have hr0 : r ≠ 0 := by
    intro h0
    rw [h0, zero_pow hp.out.ne_zero, sub_zero, mul_eq_zero] at hinj
    exact hs0 (pow_eq_zero_iff hp.out.ne_zero |>.mp (hinj.resolve_left X_ne_zero))
  have hdeg : (X * s ^ p).natDegree = (r ^ p : K[X]).natDegree := by
    have := sub_eq_zero.mp hinj; rw [this]
  rw [natDegree_mul X_ne_zero (pow_ne_zero _ hs0), natDegree_X, natDegree_pow,
    natDegree_pow] at hdeg
  refine absurd (Nat.le_of_dvd Nat.one_pos ?_) hp.out.one_lt.not_ge
  refine ⟨r.natDegree - s.natDegree, ?_⟩
  have h1 : p * r.natDegree - p * s.natDegree = 1 := by omega
  rw [Nat.mul_sub, h1]
private lemma adjoin_genT_over_frobeniusSubfield
  [PerfectField K] (t : M) [ExpChar (↥K⟮t⟯) p] :
  (IntermediateField.adjoin (↥(frobeniusSubfield (↥K⟮t⟯) p)) {genT t} :
    IntermediateField _ (↥K⟮t⟯)) = ⊤ := by
  let _ : ExpChar (↥K⟮t⟯) p :=
    expChar_of_injective_algebraMap (algebraMap K _).injective p
  rw [eq_top_iff]
  intro x _
  obtain ⟨r, s, hrs⟩ := (IntermediateField.mem_adjoin_simple_iff K _).mp x.2
  have hrs' : x = aeval (genT t) r / aeval (genT t) s := by
    apply Subtype.ext
    rw [hrs]
    push_cast
    exact congrArg₂ _
      (IntermediateField.AdjoinSimple.coe_aeval_gen_apply (F := K) (α := t) r).symm
      (IntermediateField.AdjoinSimple.coe_aeval_gen_apply (F := K) (α := t) s).symm
  rw [hrs']
  have hK : ∀ c : K, (algebraMap K (↥K⟮t⟯)) c ∈ (frobeniusSubfield (↥K⟮t⟯) p : Subfield _) := by
    intro c
    obtain ⟨c', hc'⟩ := (frobeniusEquiv K p).surjective c
    exact ⟨algebraMap K _ c', by
      rw [← hc']; simp [frobenius_def, map_pow, frobeniusEquiv_apply, frobenius_def]⟩
  have haeval : ∀ q : K[X], aeval (genT t) q ∈
    (IntermediateField.adjoin (↥(frobeniusSubfield (↥K⟮t⟯) p)) {genT t} :
        IntermediateField _ (↥K⟮t⟯)) := by
    intro q
    refine Polynomial.induction_on q ?_ ?_ ?_
    ·
      intro c
      simp [aeval_C]
      apply IntermediateField.algebraMap_mem _
        (⟨_, hK c⟩ : ↥(frobeniusSubfield (↥K⟮t⟯) p))
    ·
      intro f g hf hg
      simpa [map_add] using add_mem hf hg
    ·
      intro n c _
      simp [map_mul, aeval_C, map_pow, aeval_X]
      apply mul_mem (IntermediateField.algebraMap_mem _
          (⟨_, hK c⟩ : ↥(frobeniusSubfield (↥K⟮t⟯) p)))
        (pow_mem (IntermediateField.mem_adjoin_simple_self _ _) _)
  exact div_mem (haeval r) (haeval s)
private lemma finrank_frobeniusSubfield_adjoin_transcendental
  [PerfectField K] {t : M} (htr : Transcendental K t)
  [ExpChar (↥(IntermediateField.adjoin K ({t} : Set M))) p] :
  Module.finrank
    (frobeniusSubfield (↥(IntermediateField.adjoin K ({t} : Set M))) p)
      (↥(IntermediateField.adjoin K ({t} : Set M))) = p := by
  let _ : ExpChar (↥K⟮t⟯) p :=
    expChar_of_injective_algebraMap (algebraMap K _).injective p
  let _ : CharP (↥K⟮t⟯) p :=
    charP_of_injective_algebraMap (algebraMap K _).injective p
  let t' : ↥K⟮t⟯ := genT t
  let tp : ↥(frobeniusSubfield (↥K⟮t⟯) p) := ⟨t' ^ p, pow_mem_frobeniusSubfield p t'⟩
  have hint : IsIntegral (↥(frobeniusSubfield (↥K⟮t⟯) p)) t' := by
    refine ⟨X ^ p - C tp, monic_X_pow_sub_C _ hp.out.ne_zero, ?_⟩
    simp [eval₂_sub, eval₂_X_pow, eval₂_C]
    exact sub_eq_zero.mpr rfl
  let hfd : FiniteDimensional (↥(frobeniusSubfield (↥K⟮t⟯) p)) (↥K⟮t⟯) := by
    have h1 := adjoin_genT_over_frobeniusSubfield (K := K) (M := M) p t
    have h2 := IntermediateField.adjoin.finiteDimensional hint
    rw [show t' = genT t from rfl, h1] at h2
    exact (IntermediateField.topEquiv (F := ↥(frobeniusSubfield (↥K⟮t⟯) p))
      (E := ↥K⟮t⟯)).toLinearEquiv.finiteDimensional
  have hli := pDigits_linearIndependent (M := ↥K⟮t⟯) p (t := t') (genT_not_pow p t htr)
  refine le_antisymm ?_
    (by simpa [Fintype.card_fin] using hli.fintype_card_le_finrank)
  have htop := adjoin_genT_over_frobeniusSubfield (K := K) (M := M) p t
  calc
    _ = Module.finrank (↥(frobeniusSubfield (↥K⟮t⟯) p))
      (↥(IntermediateField.adjoin (↥(frobeniusSubfield (↥K⟮t⟯) p)) {t'} :
        IntermediateField _ (↥K⟮t⟯))) := by
      rw [show t' = genT t from rfl, htop, IntermediateField.finrank_top']
    _ = (minpoly (↥(frobeniusSubfield (↥K⟮t⟯) p)) t').natDegree :=
      IntermediateField.adjoin.finrank hint
    _ ≤ (X ^ p - C tp).natDegree := by
      apply Polynomial.natDegree_le_of_dvd
      ·
        apply minpoly.dvd
        simp [map_sub, map_pow, aeval_X, aeval_C]
        apply sub_eq_zero.mpr rfl
      · apply (monic_X_pow_sub_C _ hp.out.ne_zero).ne_zero
    _ = p := natDegree_X_pow_sub_C

end AdjoinIndex

private lemma finrank_frobeniusSubfield_eq_of_transcendental
  {K M : Type*} [Field K] [Field M]
  [Algebra K M] [PerfectField K] (p : ℕ) [hp : Fact p.Prime] [CharP K p]
  (t : M) (htr : Transcendental K t)
  [FiniteDimensional (IntermediateField.adjoin K ({t} : Set M)) M]
  [ExpChar M p] :
  Module.finrank (frobeniusSubfield M p) M = p := by
  let _ : ExpChar M p := expChar_of_injective_algebraMap (algebraMap K M).injective p
  let _ : ExpChar (↥(IntermediateField.adjoin K ({t} : Set M))) p :=
    expChar_of_injective_algebraMap (algebraMap K _).injective p
  have hpos : 0 < Module.finrank
    (frobeniusSubfield (↥(IntermediateField.adjoin K ({t} : Set M))) p)
      (↥(IntermediateField.adjoin K ({t} : Set M))) := by
    rw [finrank_frobeniusSubfield_adjoin_transcendental p htr]
    apply hp.out.pos
  let _ : FiniteDimensional
    (frobeniusSubfield (↥(IntermediateField.adjoin K ({t} : Set M))) p)
      (↥(IntermediateField.adjoin K ({t} : Set M))) :=
    FiniteDimensional.of_finrank_pos hpos
  rw [finrank_frobeniusSubfield_eq (E := ↥(IntermediateField.adjoin K ({t} : Set M))) p,
    finrank_frobeniusSubfield_adjoin_transcendental p htr]
section PDigitsExists
variable {M : Type*} [Field M] (p : ℕ) [hp : Fact p.Prime] [CharP M p] [ExpChar M p]
private lemma pDigits_exists_of_finrank_eq
  (hfr : Module.finrank (frobeniusSubfield M p) M = p)
    {t : M} (htp : ∀ a : M, a ^ p ≠ t) (g : M) :
    ∃ a : Fin p → M, g = ∑ i : Fin p, a i ^ p * t ^ (i : ℕ) := by
  let _ : ExpChar M p := ExpChar.prime hp.out
  have hlin := pDigits_linearIndependent p htp
  let b : Module.Basis (Fin p) (frobeniusSubfield M p) M :=
    basisOfLinearIndependentOfCardEqFinrank hlin (by rw [hfr, Fintype.card_fin])
  have hbapply : ∀ i : Fin p, (b i : M) = t ^ (i : ℕ) := fun i =>
    congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hlin
      (by rw [hfr, Fintype.card_fin])) i
  refine ⟨fun i => (frobeniusRingEquivRange M p).symm (b.repr g i), ?_⟩
  conv_lhs => rw [← b.sum_repr g]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hbapply i, ← frobeniusRingEquivRange_apply M p, RingEquiv.apply_symm_apply]
  rfl

end PDigitsExists

private lemma pDigits_existsUnique_of_transcendental
  {K M : Type*} [Field K] [Field M]
  [Algebra K M] [PerfectField K] (p : ℕ) [hp : Fact p.Prime] [CharP K p]
  (t : M) (htr : Transcendental K t)
  [FiniteDimensional (IntermediateField.adjoin K ({t} : Set M)) M]
  (htp : ∀ a : M, a ^ p ≠ t) (g : M) :
    ∃! a : Fin p → M, g = ∑ i : Fin p, a i ^ p * t ^ (i : ℕ) := by
  let _ : CharP M p := charP_of_injective_algebraMap (algebraMap K M).injective p
  let _ : ExpChar M p := ExpChar.prime hp.out
  have hlin := pDigits_linearIndependent p htp
  have hfr := finrank_frobeniusSubfield_eq_of_transcendental p t htr
  let b : Module.Basis (Fin p) (frobeniusSubfield M p) M :=
    basisOfLinearIndependentOfCardEqFinrank hlin (by rw [hfr, Fintype.card_fin])
  have hbapply : ∀ i : Fin p, (b i : M) = t ^ (i : ℕ) := fun i =>
    congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hlin
      (by rw [hfr, Fintype.card_fin])) i
  have hexpand : ∀ (c : Fin p → M),
      ∑ i : Fin p, c i ^ p * t ^ (i : ℕ) =
        ∑ i : Fin p, (frobeniusRingEquivRange M p (c i) : frobeniusSubfield M p) • b i := by
    intro c
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hbapply i, Subfield.smul_def, frobeniusRingEquivRange_apply, smul_eq_mul]
  obtain ⟨a, ha⟩ := pDigits_exists_of_finrank_eq p hfr htp g
  refine ⟨a, ha, ?_⟩
  intro a' ha'
  have key : ∀ i, frobeniusRingEquivRange M p (a i) = frobeniusRingEquivRange M p (a' i) := by
    intro i
    have hga : g = ∑ j : Fin p, (frobeniusRingEquivRange M p (a j) :
        frobeniusSubfield M p) • b j := ha.trans (hexpand a)
    have hga' : g = ∑ j : Fin p, (frobeniusRingEquivRange M p (a' j) :
        frobeniusSubfield M p) • b j := ha'.trans (hexpand a')
    have hra := b.repr_sum_self
      (c := fun j => (frobeniusRingEquivRange M p (a j) : frobeniusSubfield M p))
    have hra' := b.repr_sum_self
      (c := fun j => (frobeniusRingEquivRange M p (a' j) : frobeniusSubfield M p))
    rw [← hga] at hra
    rw [← hga'] at hra'
    exact congrFun (hra.symm.trans hra') i
  funext i
  exact (frobeniusRingEquivRange M p).injective (key i).symm

/--
[AlgebraicCurve_finrank_frobeniusSubfield_eq_of_transcendental](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicCurve_finrank_frobeniusSubfield_eq_of_transcendental.lean)
-/
@[path]
private lemma main
  [Field K] [Field M] [Algebra K M] [PerfectField K]
  (p : ℕ) [hp : Fact p.Prime] [CharP K p] [ExpChar M p]
  {t : M} [FiniteDimensional (IntermediateField.adjoin K ({t} : Set M)) M]
-- given
  (htr : Transcendental K t) :
-- imply
  Module.finrank ↥(frobenius M p).fieldRange M = p := by
-- proof
  apply finrank_frobeniusSubfield_eq_of_transcendental p t htr


-- created on 2026-10-20
