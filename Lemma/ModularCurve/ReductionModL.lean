import Mathlib
import Lemma.ModularCurve.ArithmeticGalois
import Lemma.ModularCurve.X0ModL

set_option autoImplicit false

noncomputable section

open HahnSeries IntermediateField AlgebraicCurve

namespace ModularCurve

section Spec

variable {L : Type*} [Field L] [Algebra ℚ L] (A : ValuationSubring L)
variable {k : Type*} [Field k] (π : A →+* k) (N : ℕ)

def IsPlaceReductionAlong
    (r : Place L (laurentBaseChange L (modularFunctionFieldFull N)) →
      Place k (modularFunctionFieldFullC k N)) : Prop :=
  (∀ P, (r P).deg = P.deg) ∧
    ∀ (y : LaurentSeries A)
      (hy : coeffMap A.subtype y ∈ laurentBaseChange L (modularFunctionFieldFull N))
      (hyk : coeffMap π y ∈ modularFunctionFieldFullC k N),
      coeffMap π y ≠ 0 →
        ∀ D : Divisor L (laurentBaseChange L (modularFunctionFieldFull N)),
          (∀ P, D P = P.ord (⟨coeffMap A.subtype y, hy⟩ : laurentBaseChange L (modularFunctionFieldFull N))) →
            ∀ Q, Finsupp.mapDomain r D Q = Q.ord (⟨coeffMap π y, hyk⟩ : modularFunctionFieldFullC k N)

def integralPrincipalDivisors : Set (Divisor L (laurentBaseChange L (modularFunctionFieldFull N))) :=
  {D | ∃ (y : LaurentSeries A)
      (hy : coeffMap A.subtype y ∈ laurentBaseChange L (modularFunctionFieldFull N)),
      coeffMap π y ∈ modularFunctionFieldFullC k N ∧ coeffMap π y ≠ 0 ∧
        ∀ P, D P = P.ord (⟨coeffMap A.subtype y, hy⟩ : laurentBaseChange L (modularFunctionFieldFull N))}

def PrincipalGeneratedByIntegral : Prop :=
  Divisor.principal (K := L) (F := laurentBaseChange L (modularFunctionFieldFull N)) ≤
    AddSubgroup.closure (integralPrincipalDivisors A π N)

def ReductionInputsAlong : Prop :=
  ∃ r, IsPlaceReductionAlong A π N r ∧ PrincipalGeneratedByIntegral A π N

end Spec

section SpecLemmas

variable {L : Type*} [Field L] [Algebra ℚ L] {A : ValuationSubring L}
variable {k : Type*} [Field k] {π : A →+* k} {N : ℕ}
variable {r : Place L (laurentBaseChange L (modularFunctionFieldFull N)) →
  Place k (modularFunctionFieldFullC k N)}

theorem IsPlaceReductionAlong.deg_eq (hr : IsPlaceReductionAlong A π N r)
    (P : Place L (laurentBaseChange L (modularFunctionFieldFull N))) : (r P).deg = P.deg :=
  hr.1 P

theorem IsPlaceReductionAlong.isPrincipal_mapDomain (hr : IsPlaceReductionAlong A π N r)
    {D : Divisor L (laurentBaseChange L (modularFunctionFieldFull N))}
    (hD : D ∈ integralPrincipalDivisors A π N) :
    Divisor.IsPrincipal (Finsupp.mapDomain r D) := by
  obtain ⟨y, hy, hyk, hne, hDy⟩ := hD
  refine ⟨⟨coeffMap π y, hyk⟩, fun h => hne (congrArg Subtype.val h), fun Q => ?_⟩
  exact hr.2 y hy hyk hne D hDy Q

theorem degree_mapDomain_of_deg_eq
    (hdeg : ∀ P, (r P).deg = P.deg)
    (D : Divisor L (laurentBaseChange L (modularFunctionFieldFull N))) :
    Divisor.degree (Finsupp.mapDomain r D) = Divisor.degree D := by
  induction D using Finsupp.induction with
  | zero => simp
  | single_add P n D _ _ ih =>
    rw [Finsupp.mapDomain_add, map_add, map_add, ih, Finsupp.mapDomain_single,
      Divisor.degree_single, Divisor.degree_single, hdeg]

theorem mapDomain_mem_degZero_of_deg_eq
    (hdeg : ∀ P, (r P).deg = P.deg)
    {D : Divisor L (laurentBaseChange L (modularFunctionFieldFull N))}
    (hD : D ∈ Divisor.degZero (K := L) (F := laurentBaseChange L (modularFunctionFieldFull N))) :
    Finsupp.mapDomain r D ∈ Divisor.degZero (K := k) (F := modularFunctionFieldFullC k N) := by
  rw [Divisor.mem_degZero] at hD ⊢
  rw [degree_mapDomain_of_deg_eq hdeg, hD]

theorem IsPlaceReductionAlong.mapDomain_mem_principal (hr : IsPlaceReductionAlong A π N r)
    (hgen : PrincipalGeneratedByIntegral A π N)
    {D : Divisor L (laurentBaseChange L (modularFunctionFieldFull N))}
    (hD : D ∈ Divisor.principal (K := L) (F := laurentBaseChange L (modularFunctionFieldFull N))) :
    Finsupp.mapDomain r D ∈ Divisor.principal (K := k) (F := modularFunctionFieldFullC k N) := by
  have hD' := hgen hD
  clear hD
  induction hD' using AddSubgroup.closure_induction with
  | mem E hE => exact hr.isPrincipal_mapDomain hE
  | zero => rw [Finsupp.mapDomain_zero]; exact AddSubgroup.zero_mem _
  | add E E' _ _ hE hE' => rw [Finsupp.mapDomain_add]; exact AddSubgroup.add_mem _ hE hE'
  | neg E _ hE =>
    rw [← Finsupp.mapDomain.addMonoidHom_apply, map_neg, Finsupp.mapDomain.addMonoidHom_apply]
    exact AddSubgroup.neg_mem _ hE

end SpecLemmas

section Descent

variable {L : Type*} [Field L] [Algebra ℚ L] {A : ValuationSubring L}
variable {k : Type*} [Field k] {π : A →+* k} {N : ℕ}
variable (r : Place L (laurentBaseChange L (modularFunctionFieldFull N)) →
  Place k (modularFunctionFieldFullC k N))

def reductionDivAlong :
    Divisor L (laurentBaseChange L (modularFunctionFieldFull N)) →+ Divisor k (modularFunctionFieldFullC k N) :=
  Finsupp.mapDomain.addMonoidHom r

@[simp]
theorem reductionDivAlong_apply (D : Divisor L (laurentBaseChange L (modularFunctionFieldFull N))) :
    reductionDivAlong r D = Finsupp.mapDomain r D :=
  rfl

theorem reductionDivAlong_single (P : Place L (laurentBaseChange L (modularFunctionFieldFull N))) (n : ℤ) :
    reductionDivAlong r (Finsupp.single P n) = Finsupp.single (r P) n :=
  Finsupp.mapDomain_single

def reductionDegZeroAlong (hdeg : ∀ P, (r P).deg = P.deg) :
    Divisor.degZero (K := L) (F := laurentBaseChange L (modularFunctionFieldFull N)) →+
      Divisor.degZero (K := k) (F := modularFunctionFieldFullC k N) :=
  ((reductionDivAlong r).domRestrict _).codRestrict _ fun D => mapDomain_mem_degZero_of_deg_eq hdeg D.2

@[simp]
theorem coe_reductionDegZeroAlong (hdeg : ∀ P, (r P).deg = P.deg)
    (D : Divisor.degZero (K := L) (F := laurentBaseChange L (modularFunctionFieldFull N))) :
    (reductionDegZeroAlong r hdeg D : Divisor k (modularFunctionFieldFullC k N)) =
      Finsupp.mapDomain r (D : Divisor L (laurentBaseChange L (modularFunctionFieldFull N))) :=
  rfl

def reductionPic0Along (hr : IsPlaceReductionAlong A π N r) (hgen : PrincipalGeneratedByIntegral A π N) :
    Pic0 L (laurentBaseChange L (modularFunctionFieldFull N)) →+ JZeroC k N :=
  QuotientAddGroup.map _ _ (reductionDegZeroAlong r hr.1) (by
    rintro ⟨D, hD0⟩ hD
    simp only [AddSubgroup.mem_addSubgroupOf] at hD ⊢
    exact hr.mapDomain_mem_principal hgen hD)

theorem reductionPic0Along_mk (hr : IsPlaceReductionAlong A π N r)
    (hgen : PrincipalGeneratedByIntegral A π N)
    (D : Divisor.degZero (K := L) (F := laurentBaseChange L (modularFunctionFieldFull N))) :
    reductionPic0Along r hr hgen (Pic0.mk D) = Pic0.mk (reductionDegZeroAlong r hr.1 D) :=
  rfl

end Descent

section Total

variable {L : Type*} [Field L] [Algebra ℚ L] (A : ValuationSubring L)
variable {k : Type*} [Field k] (π : A →+* k) (N : ℕ)

open Classical in

def reductionAlong : Pic0 L (laurentBaseChange L (modularFunctionFieldFull N)) →+ JZeroC k N :=
  if h : ReductionInputsAlong A π N then reductionPic0Along h.choose h.choose_spec.1 h.choose_spec.2 else 0

variable {A π N}

theorem reductionAlong_eq (h : ReductionInputsAlong A π N) :
    reductionAlong A π N = reductionPic0Along h.choose h.choose_spec.1 h.choose_spec.2 := by
  rw [reductionAlong, dif_pos h]

theorem reductionAlong_mk (h : ReductionInputsAlong A π N)
    (D : Divisor.degZero (K := L) (F := laurentBaseChange L (modularFunctionFieldFull N))) :
    reductionAlong A π N (Pic0.mk D) = Pic0.mk (reductionDegZeroAlong h.choose h.choose_spec.1.1 D) := by
  rw [reductionAlong_eq h]
  rfl

theorem reductionAlong_of_not (h : ¬ ReductionInputsAlong A π N) : reductionAlong A π N = 0 := by
  rw [reductionAlong, dif_neg h]

end Total

section CharL

set_option synthInstance.maxHeartbeats 400000

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (N : ℕ)

abbrev IsPlaceReductionModL
    (r : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) →
      Place (IsLocalRing.ResidueField A) (modularFunctionFieldFullC (IsLocalRing.ResidueField A) N)) : Prop :=
  IsPlaceReductionAlong A (IsLocalRing.residue A) N r

abbrev ReductionInputsModL : Prop :=
  ReductionInputsAlong A (IsLocalRing.residue A) N

variable {A N} in

def placeReductionModL (h : ReductionInputsModL A N) :
    Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) →
      Place (IsLocalRing.ResidueField A) (modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) :=
  h.choose

variable {A N} in
theorem isPlaceReductionModL_placeReductionModL (h : ReductionInputsModL A N) :
    IsPlaceReductionModL A N (placeReductionModL h) :=
  h.choose_spec.1

abbrev reductionModL : JZero N →+ JZeroC (IsLocalRing.ResidueField A) N :=
  reductionAlong A (IsLocalRing.residue A) N

variable {A N} in
theorem reductionModL_mk (h : ReductionInputsModL A N)
    (D : Divisor.degZero (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar N)) :
    reductionModL A N (Pic0.mk D) =
      Pic0.mk (reductionDegZeroAlong (placeReductionModL h)
        (isPlaceReductionModL_placeReductionModL h).1 D) :=
  reductionAlong_mk h D

variable {A N} in
theorem reductionModL_of_not (h : ¬ ReductionInputsModL A N) : reductionModL A N = 0 :=
  reductionAlong_of_not h

end CharL

section Uniqueness

variable {L : Type*} [Field L] [Algebra ℚ L] {A : ValuationSubring L}
variable {k : Type*} [Field k] {π : A →+* k} {N : ℕ}

private theorem int_eq_zero_of_forall_dvd {a : ℤ} (h : ∀ n : ℕ, n ≠ 0 → (n : ℤ) ∣ a) : a = 0 :=
  Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (h (a.natAbs + 1) (Nat.succ_ne_zero _))
    (by rw [Int.natAbs_natCast]; exact Nat.lt_succ_self _)

theorem IsPlaceReductionAlong.eq_or_const_of_agree
    {r₁ r₂ : Place L (laurentBaseChange L (modularFunctionFieldFull N)) →
      Place k (modularFunctionFieldFullC k N)}
    (hgen : PrincipalGeneratedByIntegral A π N)
    (hagree : ∀ D ∈ integralPrincipalDivisors A π N, Finsupp.mapDomain r₁ D = Finsupp.mapDomain r₂ D)
    (hdeg : ∀ P : Place L (laurentBaseChange L (modularFunctionFieldFull N)), P.deg = 1)
    (hdiv : ∀ n : ℕ, n ≠ 0 → ∀ x : Pic0 L (laurentBaseChange L (modularFunctionFieldFull N)),
      ∃ y : Pic0 L (laurentBaseChange L (modularFunctionFieldFull N)), n • y = x) :
    r₁ = r₂ ∨ ∀ P Q, r₁ P = r₁ Q := by
  classical

  set δ : Divisor L (laurentBaseChange L (modularFunctionFieldFull N)) →+
      Divisor k (modularFunctionFieldFullC k N) :=
    Finsupp.mapDomain.addMonoidHom r₁ - Finsupp.mapDomain.addMonoidHom r₂ with hδ
  have hδapp : ∀ D, δ D = Finsupp.mapDomain r₁ D - Finsupp.mapDomain r₂ D := fun D => rfl

  have hδprin : ∀ D ∈ Divisor.principal (K := L) (F := laurentBaseChange L (modularFunctionFieldFull N)),
      δ D = 0 := by
    intro D hD
    have hD' := hgen hD
    clear hD
    induction hD' using AddSubgroup.closure_induction with
    | mem E hE => rw [hδapp, hagree E hE, sub_self]
    | zero => exact map_zero δ
    | add E E' _ _ hE hE' => rw [map_add, hE, hE', add_zero]
    | neg E _ hE => rw [map_neg, hE, neg_zero]

  have hδdeg0 : ∀ D ∈ Divisor.degZero (K := L) (F := laurentBaseChange L (modularFunctionFieldFull N)),
      δ D = 0 := by
    intro D hD
    ext Q
    rw [Finsupp.zero_apply]
    refine int_eq_zero_of_forall_dvd fun n hn => ?_
    obtain ⟨y, hy⟩ := hdiv n hn (Pic0.mk ⟨D, hD⟩)
    obtain ⟨E, rfl⟩ := Pic0.mk_surjective y

    have hmem : ((⟨D, hD⟩ : Divisor.degZero (K := L) (F := laurentBaseChange L (modularFunctionFieldFull N)))
        - n • E : Divisor.degZero (K := L) (F := laurentBaseChange L (modularFunctionFieldFull N))) ∈
          (Divisor.principal (K := L) (F := laurentBaseChange L (modularFunctionFieldFull N))).addSubgroupOf
            (Divisor.degZero (K := L) (F := laurentBaseChange L (modularFunctionFieldFull N))) := by
      rw [← QuotientAddGroup.eq_iff_sub_mem, QuotientAddGroup.mk_nsmul]
      exact hy.symm
    rw [AddSubgroup.mem_addSubgroupOf, AddSubgroupClass.coe_sub, AddSubgroupClass.coe_nsmul] at hmem
    have h0 := hδprin _ hmem
    rw [map_sub, map_nsmul, sub_eq_zero] at h0
    refine ⟨δ (E : Divisor L (laurentBaseChange L (modularFunctionFieldFull N))) Q, ?_⟩
    rw [h0, Finsupp.smul_apply, nsmul_eq_mul]

  have hconst : ∀ P Q : Place L (laurentBaseChange L (modularFunctionFieldFull N)),
      Finsupp.single (r₁ P) (1 : ℤ) - Finsupp.single (r₂ P) 1 =
        Finsupp.single (r₁ Q) 1 - Finsupp.single (r₂ Q) 1 := by
    intro P Q
    have hPQ : Finsupp.single P (1 : ℤ) - Finsupp.single Q 1 ∈
        Divisor.degZero (K := L) (F := laurentBaseChange L (modularFunctionFieldFull N)) := by
      rw [Divisor.mem_degZero, map_sub, Divisor.degree_single, Divisor.degree_single, hdeg, hdeg, sub_self]
    have h := hδdeg0 _ hPQ
    rw [hδapp, Finsupp.mapDomain_sub, Finsupp.mapDomain_sub, Finsupp.mapDomain_single,
      Finsupp.mapDomain_single, Finsupp.mapDomain_single, Finsupp.mapDomain_single, sub_eq_zero] at h
    exact sub_eq_sub_iff_sub_eq_sub.mpr h

  rw [or_iff_not_imp_left]
  intro hne
  obtain ⟨P₀, hP₀⟩ : ∃ P₀, r₁ P₀ ≠ r₂ P₀ := by
    by_contra hall
    push Not at hall
    exact hne (funext hall)
  have hr₁const : ∀ Q, r₁ Q = r₁ P₀ := by
    intro Q
    have h := congrArg (fun E => E (r₁ P₀)) (hconst Q P₀)
    simp only [Finsupp.sub_apply, Finsupp.single_apply, if_neg (Ne.symm hP₀)] at h
    by_contra hQ
    rw [if_neg hQ] at h
    split_ifs at h <;> omega
  exact fun P Q => (hr₁const P).trans (hr₁const Q).symm

theorem IsPlaceReductionAlong.eq_of_agree
    {r₁ r₂ : Place L (laurentBaseChange L (modularFunctionFieldFull N)) →
      Place k (modularFunctionFieldFullC k N)}
    (hgen : PrincipalGeneratedByIntegral A π N)
    (hagree : ∀ D ∈ integralPrincipalDivisors A π N, Finsupp.mapDomain r₁ D = Finsupp.mapDomain r₂ D)
    (hdeg : ∀ P : Place L (laurentBaseChange L (modularFunctionFieldFull N)), P.deg = 1)
    (hprin0 : ∀ D ∈ Divisor.principal (K := L) (F := laurentBaseChange L (modularFunctionFieldFull N)),
      Divisor.degree D = 0)
    (hdiv : ∀ n : ℕ, n ≠ 0 → ∀ x : Pic0 L (laurentBaseChange L (modularFunctionFieldFull N)),
      ∃ y : Pic0 L (laurentBaseChange L (modularFunctionFieldFull N)), n • y = x)
    (hnc : ∃ D ∈ Divisor.principal (K := L) (F := laurentBaseChange L (modularFunctionFieldFull N)),
      Finsupp.mapDomain r₁ D ≠ 0) :
    r₁ = r₂ := by
  rcases IsPlaceReductionAlong.eq_or_const_of_agree hgen hagree hdeg hdiv with h | hconst
  · exact h
  obtain ⟨D, hDprin, hDne⟩ := hnc
  obtain ⟨P₀⟩ : Nonempty (Place L (laurentBaseChange L (modularFunctionFieldFull N))) := by
    by_contra hempty
    rw [not_nonempty_iff] at hempty
    exact hDne (by rw [Subsingleton.elim D 0, Finsupp.mapDomain_zero])
  exfalso
  apply hDne
  have hmapconst : ∀ D : Divisor L (laurentBaseChange L (modularFunctionFieldFull N)),
      Finsupp.mapDomain r₁ D = Finsupp.single (r₁ P₀) (Divisor.degree D) := by
    intro D
    induction D using Finsupp.induction with
    | zero => simp
    | single_add P n D _ _ ih =>
      rw [Finsupp.mapDomain_add, ih, Finsupp.mapDomain_single, hconst P P₀, map_add,
        Divisor.degree_single, hdeg, Nat.cast_one, mul_one, ← Finsupp.single_add, add_comm]
  rw [hmapconst D, hprin0 D hDprin, Finsupp.single_zero]

end Uniqueness

end ModularCurve

end
