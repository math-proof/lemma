module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.Polynomial.ScaleRoots
public import Mathlib.Algebra.Polynomial.Lifts

public noncomputable section

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial

namespace AlgebraicCurve

namespace TwoChartIntegralModel

variable (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]

variable {F} in
public theorem j_ne_zero : j ≠ 0 := Fact.out


public theorem mem_chartAlg_iff {S : Set F} {x : F} :
    x ∈ chartAlg R F S ↔ IsIntegral (Algebra.adjoin R S) x := Iff.rfl


public theorem adjoin_le_chartAlg (S : Set F) : Algebra.adjoin R S ≤ chartAlg R F S := fun x hx => by
  rw [mem_chartAlg_iff]
  exact isIntegral_algebraMap (x := (⟨x, hx⟩ : Algebra.adjoin R S))


public theorem subset_chartAlg (S : Set F) : S ⊆ (chartAlg R F S : Set F) := fun _ hx =>
  adjoin_le_chartAlg R F S (Algebra.subset_adjoin hx)


public theorem chartAlg_mono {S S' : Set F} (h : S ⊆ S') : chartAlg R F S ≤ chartAlg R F S' := by
  intro x hx
  rw [mem_chartAlg_iff] at hx ⊢
  exact hx.map_of_comp_eq
    (Subalgebra.inclusion (Algebra.adjoin_mono h)).toRingHom (RingHom.id F) (by ext; rfl)


public theorem coe_chartIncl {S S' : Set F} (h : S ⊆ S') (x : chartAlg R F S) :
    (chartIncl R F h x : F) = x :=
  Subalgebra.coe_inclusion _ x


public theorem chartIncl_injective {S S' : Set F} (h : S ⊆ S') :
    Function.Injective (chartIncl R F h) :=
  Subalgebra.inclusion_injective _

variable {R F j}


public theorem exists_pow_mul_mem_adjoin {S : Set F} {s : F} (hs : s ∈ S) (hs0 : s ≠ 0) {x : F}
    (hx : x ∈ Algebra.adjoin R (insert s⁻¹ S)) : ∃ n : ℕ, s ^ n * x ∈ Algebra.adjoin R S := by
  have hsA : s ∈ Algebra.adjoin R S := Algebra.subset_adjoin hs
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    rcases hy with rfl | hy
    · exact ⟨1, by rw [pow_one, mul_inv_cancel₀ hs0]; exact one_mem _⟩
    · exact ⟨0, by rw [pow_zero, one_mul]; exact Algebra.subset_adjoin hy⟩
  | algebraMap a => exact ⟨0, by rw [pow_zero, one_mul]; exact Subalgebra.algebraMap_mem _ a⟩
  | add y z _ _ hy hz =>
    obtain ⟨m, hm⟩ := hy
    obtain ⟨n, hn⟩ := hz
    refine ⟨m + n, ?_⟩
    have : s ^ (m + n) * (y + z) = s ^ n * (s ^ m * y) + s ^ m * (s ^ n * z) := by ring
    rw [this]
    exact add_mem (mul_mem (pow_mem hsA n) hm) (mul_mem (pow_mem hsA m) hn)
  | mul y z _ _ hy hz =>
    obtain ⟨m, hm⟩ := hy
    obtain ⟨n, hn⟩ := hz
    refine ⟨m + n, ?_⟩
    have : s ^ (m + n) * (y * z) = (s ^ m * y) * (s ^ n * z) := by ring
    rw [this]
    exact mul_mem hm hn


public theorem exists_pow_mul_mem_chartAlg {S : Set F} {s : F} (hs : s ∈ S) (hs0 : s ≠ 0) {x : F}
    (hx : x ∈ chartAlg R F (insert s⁻¹ S)) : ∃ n : ℕ, s ^ n * x ∈ chartAlg R F S := by
  classical
  obtain ⟨p, hmonic, hroot⟩ := (mem_chartAlg_iff R F).mp hx
  have hcoeff : ∀ i, ∃ n : ℕ, s ^ n * (p.coeff i : F) ∈ Algebra.adjoin R S :=
    fun i => exists_pow_mul_mem_adjoin hs hs0 (p.coeff i).2
  choose n hn using hcoeff
  set M : ℕ := ∑ i ∈ Finset.range (p.natDegree + 1), n i with hM
  have hnM : ∀ i ≤ p.natDegree, n i ≤ M := fun i hi =>
    Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  set q : F[X] := (p.map (algebraMap (Algebra.adjoin R (insert s⁻¹ S)) F)).scaleRoots (s ^ M)
    with hq
  have hqmonic : q.Monic := (Polynomial.monic_scaleRoots_iff _).mpr (hmonic.map _)
  have hqroot : q.eval (s ^ M * x) = 0 := by
    rw [hq, Polynomial.scaleRoots_eval_mul, Polynomial.eval_map, hroot, mul_zero]
  have hqcoeff : ∀ i, q.coeff i ∈ Algebra.adjoin R S := by
    intro i
    rw [hq, Polynomial.coeff_scaleRoots, Polynomial.coeff_map, hmonic.natDegree_map]
    by_cases hi : i < p.natDegree
    · have hle : n i ≤ M * (p.natDegree - i) := by
        calc n i ≤ M := hnM i hi.le
          _ = M * 1 := (mul_one M).symm
          _ ≤ M * (p.natDegree - i) := Nat.mul_le_mul_left M (Nat.one_le_iff_ne_zero.mpr (by omega))
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
      have : (s ^ M) ^ (p.natDegree - i) = s ^ k * s ^ n i := by
        rw [← pow_mul, hk, pow_add, mul_comm]
      rw [this, Subalgebra.algebraMap_def, Algebra.algebraMap_self_apply,
        show (p.coeff i : F) * (s ^ k * s ^ n i) = s ^ k * (s ^ n i * (p.coeff i : F)) by ring]
      exact mul_mem (pow_mem (Algebra.subset_adjoin hs) k) (hn i)
    · rcases (not_lt.mp hi).lt_or_eq with hlt | heq
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt, map_zero, zero_mul]
        exact zero_mem _
      · rw [← heq, hmonic.coeff_natDegree, map_one, one_mul, Nat.sub_self, pow_zero]
        exact one_mem _
  have hlifts : q ∈ Polynomial.lifts (algebraMap (Algebra.adjoin R S) F) :=
    (Polynomial.lifts_iff_coeff_lifts q).mpr fun i => ⟨⟨q.coeff i, hqcoeff i⟩, rfl⟩
  obtain ⟨q', hq'q, -, hq'monic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts hqmonic
  refine ⟨M, (mem_chartAlg_iff R F).mpr ⟨q', hq'monic, ?_⟩⟩
  rw [Polynomial.eval₂_eq_eval_map, hq'q, hqroot]

variable (R F j)

omit [Fact (j ≠ 0)] in

public theorem sFin_subset : ({j} : Set F) ⊆ {j, j⁻¹} :=
  Set.singleton_subset_iff.mpr (Set.mem_insert _ _)

omit [Fact (j ≠ 0)] in

public theorem sInf_subset : ({j⁻¹} : Set F) ⊆ {j, j⁻¹} :=
  Set.singleton_subset_iff.mpr (Set.mem_insert_of_mem _ rfl)


@[simp] public theorem coe_jChartFin : (jChartFin R F j : F) = j := rfl
omit [Fact (j ≠ 0)] in

@[simp] public theorem coe_jInvChartInf : (jInvChartInf R F j : F) = j⁻¹ := rfl


public theorem isUnit_inclFin_jChartFin : IsUnit (inclFin R F j (jChartFin R F j)) := by
  refine .of_mul_eq_one ⟨j⁻¹, subset_chartAlg R F _ (by simp)⟩ (Subtype.ext ?_)
  rw [Subalgebra.coe_mul, Subalgebra.coe_one, coe_chartIncl, coe_jChartFin]
  exact mul_inv_cancel₀ (j_ne_zero j)


public theorem isUnit_inclInf_jInvChartInf : IsUnit (inclInf R F j (jInvChartInf R F j)) := by
  refine .of_mul_eq_one ⟨j, subset_chartAlg R F _ (by simp)⟩ (Subtype.ext ?_)
  rw [Subalgebra.coe_mul, Subalgebra.coe_one, coe_chartIncl, coe_jInvChartInf]
  exact inv_mul_cancel₀ (j_ne_zero j)


public theorem isLocalization_away_inclFin :
    let := (inclFin R F j).toRingHom.toAlgebra
    IsLocalization.Away (jChartFin R F j) (chartAlgMid R F j) := by
  let := (inclFin R F j).toRingHom.toAlgebra
  refine (isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    rw [RingHom.algebraMap_toAlgebra, map_pow]
    exact (isUnit_inclFin_jChartFin R F j).pow n
  · intro z
    have hz : (z : F) ∈ chartAlg R F (insert j⁻¹ {j}) := by
      rw [show insert j⁻¹ ({j} : Set F) = {j, j⁻¹}
        from Set.pair_comm _ _]
      exact z.2
    obtain ⟨n, hn⟩ := exists_pow_mul_mem_chartAlg (Set.mem_singleton _) (j_ne_zero j) hz
    refine ⟨(⟨j ^ n * z, hn⟩, ⟨jChartFin R F j ^ n, n, rfl⟩), Subtype.ext ?_⟩
    simp only [RingHom.algebraMap_toAlgebra, map_pow, Subalgebra.coe_mul, Subalgebra.coe_pow,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, coe_chartIncl, coe_jChartFin]
    exact mul_comm _ _
  · intro x y h
    refine ⟨1, ?_⟩
    rw [RingHom.algebraMap_toAlgebra] at h
    rw [chartIncl_injective R F _ h]


public theorem isLocalization_away_inclInf :
    let := (inclInf R F j).toRingHom.toAlgebra
    IsLocalization.Away (jInvChartInf R F j) (chartAlgMid R F j) := by
  let := (inclInf R F j).toRingHom.toAlgebra
  refine (isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    rw [RingHom.algebraMap_toAlgebra, map_pow]
    exact (isUnit_inclInf_jInvChartInf R F j).pow n
  · intro z
    have hz : (z : F) ∈ chartAlg R F (insert j⁻¹⁻¹ {j⁻¹}) := by
      rw [inv_inv]; exact z.2
    obtain ⟨n, hn⟩ := exists_pow_mul_mem_chartAlg (Set.mem_singleton _)
      (inv_ne_zero (j_ne_zero j)) hz
    refine ⟨(⟨j⁻¹ ^ n * z, hn⟩, ⟨jInvChartInf R F j ^ n, n, rfl⟩), Subtype.ext ?_⟩
    simp only [RingHom.algebraMap_toAlgebra, map_pow, Subalgebra.coe_mul, Subalgebra.coe_pow,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, coe_chartIncl, coe_jInvChartInf]
    exact mul_comm _ _
  · intro x y h
    refine ⟨1, ?_⟩
    rw [RingHom.algebraMap_toAlgebra] at h
    rw [chartIncl_injective R F _ h]


public theorem fFin_isOpenImmersion : IsOpenImmersion (fFin R F j) := by
  let := (inclFin R F j).toRingHom.toAlgebra
  have := isLocalization_away_inclFin R F j
  exact IsOpenImmersion.of_isLocalization (jChartFin R F j)


public theorem fInf_isOpenImmersion : IsOpenImmersion (fInf R F j) := by
  let := (inclInf R F j).toRingHom.toAlgebra
  have := isLocalization_away_inclInf R F j
  exact IsOpenImmersion.of_isLocalization (jInvChartInf R F j)


public theorem hasPushout_fFin_fInf : HasPushout (fFin R F j) (fInf R F j) := by
  haveI := fFin_isOpenImmersion R F j
  haveI := fInf_isOpenImmersion R F j
  infer_instance


public theorem glue_condition : fFin R F j ≫ ιFin R F j = fInf R F j ≫ ιInf R F j :=
  haveI := hasPushout_fFin_fInf R F j
  pushout.condition

omit [Fact (j ≠ 0)] in

public theorem fFin_toBase_eq_fInf_toBase :
    fFin R F j ≫ Spec.map (CommRingCat.ofHom (algebraMap R (chartAlgFin R F j))) =
      fInf R F j ≫ Spec.map (CommRingCat.ofHom (algebraMap R (chartAlgInf R F j))) := by
  have h : (inclFin R F j).toRingHom.comp (algebraMap R (chartAlgFin R F j)) =
      (inclInf R F j).toRingHom.comp (algebraMap R (chartAlgInf R F j)) :=
    RingHom.ext fun a => ((inclFin R F j).commutes a).trans ((inclInf R F j).commutes a).symm
  simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp, h]


@[reassoc (attr := simp)]
public theorem ιFin_toBase : ιFin R F j ≫ toBase R F j =
    Spec.map (CommRingCat.ofHom (algebraMap R (chartAlgFin R F j))) :=
  haveI := hasPushout_fFin_fInf R F j
  pushout.inl_desc _ _ _


@[reassoc (attr := simp)]
public theorem ιInf_toBase : ιInf R F j ≫ toBase R F j =
    Spec.map (CommRingCat.ofHom (algebraMap R (chartAlgInf R F j))) :=
  haveI := hasPushout_fFin_fInf R F j
  pushout.inr_desc _ _ _


public theorem mem_range_ιFin_or_mem_range_ιInf (x : AlgebraicCurve.TwoChartIntegralModel R F j) :
    x ∈ Set.range (ιFin R F j).base ∨ x ∈ Set.range (ιInf R F j).base := by
  haveI := fFin_isOpenImmersion R F j
  haveI := fInf_isOpenImmersion R F j
  obtain ⟨i, y, hy⟩ :=
    (Scheme.IsLocallyDirected.openCover (span (fFin R F j) (fInf R F j))).exists_eq x
  rcases i with (_ | _ | _)
  · have hw : (Scheme.IsLocallyDirected.openCover (span (fFin R F j) (fInf R F j))).f none =
        fFin R F j ≫ ιFin R F j :=
      (colimit.w (span (fFin R F j) (fInf R F j)) WalkingSpan.Hom.fst).symm
    refine Or.inl ⟨(fFin R F j).base y, ?_⟩
    rw [← hy, hw]; rfl
  · exact Or.inl ⟨y, hy⟩
  · exact Or.inr ⟨y, hy⟩


public theorem ιFin_isOpenImmersion : IsOpenImmersion (ιFin R F j) :=
  haveI := fFin_isOpenImmersion R F j
  haveI := fInf_isOpenImmersion R F j
  (Scheme.IsLocallyDirected.openCover (span (fFin R F j) (fInf R F j))).map_prop WalkingSpan.left


public theorem ιInf_isOpenImmersion : IsOpenImmersion (ιInf R F j) :=
  haveI := fFin_isOpenImmersion R F j
  haveI := fInf_isOpenImmersion R F j
  (Scheme.IsLocallyDirected.openCover (span (fFin R F j) (fInf R F j))).map_prop WalkingSpan.right


public theorem isAffineOpen_chartFinOpen : IsAffineOpen (chartFinOpen R F j) :=
  haveI := ιFin_isOpenImmersion R F j
  isAffineOpen_opensRange (ιFin R F j)


public theorem isAffineOpen_chartInfOpen : IsAffineOpen (chartInfOpen R F j) :=
  haveI := ιInf_isOpenImmersion R F j
  isAffineOpen_opensRange (ιInf R F j)


public theorem twoChartCover : chartFinOpen R F j ⊔ chartInfOpen R F j = ⊤ := by
  rw [chartFinOpen, chartInfOpen, ← TopologicalSpace.Opens.coe_inj]
  ext x
  simpa using mem_range_ιFin_or_mem_range_ιInf R F j x


@[simp] public theorem polynomialToChartFin_X : polynomialToChartFin R F j Polynomial.X = jChartFin R F j :=
  Polynomial.aeval_X _

omit [Fact (j ≠ 0)] in

@[simp] public theorem polynomialToChartInf_X : polynomialToChartInf R F j Polynomial.X = jInvChartInf R F j :=
  Polynomial.aeval_X _


@[reassoc]
public theorem baseChangeι_toBase (S : Type u) [CommRing S] [Algebra R S] :
    baseChangeι R F j S ≫ toBase R F j =
      baseChangeToBase R F j S ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) :=
  pullback.condition


@[reassoc]
public theorem fibreι_toBase (I : Ideal R) :
    fibreι R F j I ≫ toBase R F j =
      fibreToBase R F j I ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) :=
  pullback.condition

section BaseChange

variable (R' : Type u) [CommRing R'] [Algebra R R'] [Algebra R' F] [IsScalarTower R R' F]


public theorem adjoin_le_adjoin_restrictScalars (S : Set F) :
    Algebra.adjoin R S ≤ (Algebra.adjoin R' S).restrictScalars R :=
  Algebra.adjoin_le Algebra.subset_adjoin


public theorem chartAlg_le_chartAlg (S : Set F) :
    (chartAlg R F S).toSubring ≤ (chartAlg R' F S).toSubring := by
  intro x hx
  change IsIntegral (Algebra.adjoin R' S) x
  have hx' : IsIntegral (Algebra.adjoin R S) x := hx
  have hle : (Algebra.adjoin R S).toSubring ≤ ((Algebra.adjoin R' S).restrictScalars R).toSubring :=
    fun y hy => adjoin_le_adjoin_restrictScalars R F R' S hy
  exact hx'.map_of_comp_eq (Subring.inclusion hle) (RingHom.id F) (by ext; rfl)


public theorem chartAlg_le_restrictScalars (S : Set F) :
    chartAlg R F S ≤ (chartAlg R' F S).restrictScalars R :=
  fun _ hx => chartAlg_le_chartAlg R F R' S hx


@[simp] public theorem coe_chartBaseChange (S : Set F) (x : chartAlg R F S) :
    (chartBaseChange R F R' S x : F) = x :=
  Subalgebra.coe_inclusion _ x


public theorem chartBaseChange_algebraMap (S : Set F) (r : R) :
    chartBaseChange R F R' S (algebraMap R (chartAlg R F S) r) =
      algebraMap R' (chartAlg R' F S) (algebraMap R R' r) :=
  Subtype.ext (IsScalarTower.algebraMap_apply R R' F r)

end BaseChange

end TwoChartIntegralModel

end AlgebraicCurve

end
