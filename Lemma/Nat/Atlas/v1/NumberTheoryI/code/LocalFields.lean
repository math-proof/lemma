import Mathlib
import sympy.Basic
import Def.v1.Atlas.NumberTheoryI.code.LocalFields.Part9
open Metric Filter Set Topology PowerSeries Finset in
open scoped Valued
open NumberField NumberField.InfinitePlace.Completion IsDedekindDomain


/--
[isLocalField_iff_closedBalls_compact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalFields.lean)
-/
@[path]
lemma isLocalField_iff_closedBalls_compact
  {K : Type*}
  [NontriviallyNormedField K] :
-- imply
  LocallyCompactSpace K ↔ ∀ (x : K) (r : ℝ), IsCompact (closedBall x r) := by
-- proof
  constructor
  · intro hlc
    haveI : ProperSpace K := ProperSpace.of_locallyCompactSpace K
    exact fun x r => isCompact_closedBall x r
  · intro h
    haveI : ProperSpace K := ⟨h⟩
    exact locallyCompact_of_proper

/--
[IsLocalField.completeSpace](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalFields.lean)
-/
@[path]
lemma IsLocalField.completeSpace
  {K : Type*}
  [IsLocalField K] :
-- imply
  CompleteSpace K :=
-- proof
  complete_of_proper
section DiscreteValuationCharacterization
open scoped Valued

/--
[isLocalField_iff_complete_dvr_finiteResidue](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalFields.lean)
-/
@[path]
lemma isLocalField_iff_complete_dvr_finiteResidue
  [Field K]
  [LinearOrderedCommGroupWithZero Γ₀]
  [Valued K Γ₀]
  [(Valued.v : Valuation K Γ₀).RankOne] :
-- imply
  ProperSpace K ↔ CompleteSpace K ∧ IsDiscreteValuationRing (Valued.integer K) ∧ Empty.Finite (Valued.ResidueField K) :=
-- proof
  Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField

/--
[isLocalField_iff_complete_finiteResidue_of_dvr](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalFields.lean)
-/
@[path]
lemma isLocalField_iff_complete_finiteResidue_of_dvr
  [Field K]
  [LinearOrderedCommGroupWithZero Γ₀]
  [Valued K Γ₀]
  [(Valued.v : Valuation K Γ₀).RankOne]
  [IsDiscreteValuationRing (Valued.integer K)] :
-- imply
  ProperSpace K ↔ CompleteSpace K ∧ Empty.Finite (Valued.ResidueField K) := by
-- proof
  rw [isLocalField_iff_complete_dvr_finiteResidue]
  constructor
  · rintro ⟨h1, -, h3⟩
    exact ⟨h1, h3⟩
  · rintro ⟨h1, h3⟩
    exact ⟨h1, inferInstance, h3⟩
end DiscreteValuationCharacterization

/--
[locallyCompact_of_finiteDimensional_over_localField](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalFields.lean)
-/
@[path]
lemma locallyCompact_of_finiteDimensional_over_localField
  {K : Type*}
  [IsLocalField K]
  {L : Type*}
  [NontriviallyNormedField L]
  [NormedAlgebra K L]
  [FiniteDimensional K L] :
-- imply
  LocallyCompactSpace L := by
-- proof
  haveI : ProperSpace L := FiniteDimensional.proper K L
  exact locallyCompact_of_proper
@[reducible] noncomputable def isLocalField_real : IsLocalField ℝ := inferInstance
@[reducible] noncomputable def corollary_9_7_archimedean : IsLocalField ℝ := isLocalField_real
@[reducible] noncomputable def isLocalField_padic (p : ℕ) [Fact (Nat.Prime p)] : IsLocalField ℚ_[p] :=
  instIsLocalFieldPadic p
@[reducible] noncomputable def corollary_9_7_padic (p : ℕ) [Fact (Nat.Prime p)] : IsLocalField ℚ_[p] :=
  isLocalField_padic p
@[reducible] noncomputable def isLocalField_of_finiteDimensional_extension (K : Type*) [IsLocalField K]
  (L : Type*) [NontriviallyNormedField L] [NormedAlgebra K L] [FiniteDimensional K L] :
  IsLocalField L where
  locallyCompact := locallyCompact_of_finiteDimensional_over_localField K L
@[reducible] noncomputable def corollary_9_7_finite_extension (K : Type*) [IsLocalField K]
  (L : Type*) [NontriviallyNormedField L] [NormedAlgebra K L] [FiniteDimensional K L] :
  IsLocalField L :=
  isLocalField_of_finiteDimensional_extension K L
@[reducible] noncomputable def localField_Qp (p : ℕ) [Fact (Nat.Prime p)] :
  IsLocalField ℚ_[p] := isLocalField_padic p

/--
[IsLocalField.finiteDimensional_of_locallyCompact_module](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalFields.lean)
-/
@[path]
lemma IsLocalField.finiteDimensional_of_locallyCompact_module
  {K : Type*}
  [IsLocalField K]
  [AddCommGroup E]
  [UniformSpace E]
  [T2Space E]
  [IsUniformAddGroup E]
  [Module K E]
  [ContinuousSMul K E]
  [LocallyCompactSpace E] :
-- imply
  FiniteDimensional K E := by
-- proof
  haveI : CompleteSpace K := IsLocalField.completeSpace K
  exact FiniteDimensional.of_locallyCompactSpace K

/--
[localField_charZero_classification](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalFields.lean)
-/
@[path]
lemma localField_charZero_classification
  {L : Type*}
  [IsLocalField L]
  [CharZero L] :
-- imply
  (Nonempty (L ≃+* ℝ)) ∨ (Nonempty (L ≃+* ℂ)) ∨ (∃ (p : ℕ) (_ : Fact (Nat.Prime p)) (_ : Algebra ℚ_[p] L), FiniteDimensional ℚ_[p] L) := by
-- proof
  obtain ⟨hAlg, hCSMul⟩ | ⟨p, hp, hAlg, hCSMul⟩ := localField_charZero_normedAlgebra_structure L
  ·
    letI := hAlg; letI := hCSMul
    haveI : CompleteSpace L := complete_of_proper
    haveI : FiniteDimensional ℝ L := FiniteDimensional.of_locallyCompactSpace ℝ
    haveI : Algebra.IsAlgebraic ℝ L := Algebra.IsAlgebraic.of_finite ℝ L
    cases Real.nonempty_algEquiv_or L with
    | inl h => exact Or.inl (h.map AlgEquiv.toRingEquiv)
    | inr h => exact Or.inr (Or.inl (h.map AlgEquiv.toRingEquiv))
  ·
    letI := hAlg; letI := hCSMul; haveI := hp
    right; right
    haveI : CompleteSpace L := complete_of_proper
    exact ⟨p, hp, inferInstance, FiniteDimensional.of_locallyCompactSpace ℚ_[p]⟩

/--
[posChar_laurent_series_embedding](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalFields.lean)
-/
@[path]
lemma posChar_laurent_series_embedding
  {L : Type*}
  [IsLocalField L]
  {p : ℕ}
  [Fact (Nat.Prime p)]
  [CharP L p] :
-- imply
  ∃ (n : ℕ) (_ : 0 < n), ∃ (f : LaurentSeries (GaloisField p n) →+* L), Function.Injective f := by
-- proof
  open PowerSeries Finset in
  refine ⟨1, Nat.one_pos, ?_⟩
  obtain ⟨π, hπ_lt, hπ_pos⟩ : ∃ (π : L), ‖π‖ < 1 ∧ 0 < ‖π‖ := by
    obtain ⟨x, hx⟩ := NontriviallyNormedField.non_trivial (α := L)
    by_cases h1 : ‖x‖ < 1
    · exact ⟨x, h1, by linarith⟩
    · push Not at h1
      have hx_ne : x ≠ 0 := by intro h; rw [h, norm_zero] at hx; linarith
      exact ⟨x⁻¹, by rw [norm_inv, inv_lt_one₀ (by linarith)]; linarith,
        by rw [norm_inv]; positivity⟩
  let ι : GaloisField p 1 →+* L :=
    (ZMod.castHom (dvd_refl p) L).comp (GaloisField.equivZmodP p).toAlgHom.toRingHom
  have hι_bound : ∀ a : GaloisField p 1, ‖ι a‖ ≤ 1 := by
    intro a
    have ha_frob : a ^ p = a :=
      (GaloisField.equivZmodP p).injective (by rw [map_pow, ZMod.pow_card])
    have hia_frob : (ι a) ^ p = ι a := by rw [← map_pow, ha_frob]
    by_cases hx0 : ι a = 0
    · simp [hx0]
    · by_contra h; push Not at h
      linarith [pow_le_pow_right₀ h.le (Fact.out : Nat.Prime p).two_le,
        sq_nonneg (‖ι a‖ - 1),
        show ‖ι a‖ ^ p = ‖ι a‖ from by rw [← norm_pow, hia_frob]]
  have norm_bound : ∀ (f : PowerSeries (GaloisField p 1)) (n : ℕ),
    ‖ι (coeff n f) * π ^ n‖ ≤ ‖π‖ ^ n := by
    intro f n; rw [norm_mul, norm_pow]
    calc ‖ι (coeff n f)‖ * ‖π‖ ^ n ≤ 1 * ‖π‖ ^ n := by gcongr; exact hι_bound _
    _ = ‖π‖ ^ n := one_mul _
  have summ : ∀ f : PowerSeries (GaloisField p 1),
    Summable (fun n => ι (coeff n f) * π ^ n) := by
    intro f
    exact .of_norm_bounded (g := fun n => ‖π‖ ^ n)
      (summable_geometric_of_lt_one (norm_nonneg _) hπ_lt) (norm_bound f)
  have summ_norm : ∀ f : PowerSeries (GaloisField p 1),
    Summable (fun n => ‖ι (coeff n f) * π ^ n‖) := by
    intro f
    exact (summable_geometric_of_lt_one (norm_nonneg _) hπ_lt).of_nonneg_of_le
      (fun _ => norm_nonneg _) (norm_bound f)
  have hπ_ne : π ≠ 0 := norm_pos_iff.mp hπ_pos
  let evalPS : PowerSeries (GaloisField p 1) →+* L :=
    { toFun := fun f => ∑' n, ι (coeff n f) * π ^ n
      map_zero' := by simp only [map_zero, zero_mul, tsum_zero]
      map_one' := by
        rw [show (∑' n, ι (coeff n (1 : PowerSeries _)) * π ^ n) =
          ι (coeff 0 1) * π ^ 0 from
          tsum_eq_single 0 (fun n hn => by
            rw [coeff_one, if_neg hn, map_zero, zero_mul])]
        simp [coeff_one]
      map_add' := fun F G => by
        simp only [map_add, add_mul]
        exact (summ F).tsum_add (summ G)
      map_mul' := fun F G => by
        rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm (summ_norm F) (summ_norm G)]
        congr 1; ext n
        rw [PowerSeries.coeff_mul, map_sum ι, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro ⟨i, j⟩ hij
        have hij' : i + j = n := Finset.mem_antidiagonal.mp hij
        rw [map_mul, mul_mul_mul_comm, ← pow_add, hij'] }
  have evalPS_X_pow : ∀ k : ℕ, evalPS (PowerSeries.X ^ k) = π ^ k := by
    intro k
    show (∑' n, ι (coeff n (PowerSeries.X ^ k)) * π ^ n) = π ^ k
    rw [tsum_eq_single k (fun n hn => by
      simp only [PowerSeries.coeff_X_pow]
      rw [if_neg hn, map_zero, zero_mul])]
    rw [PowerSeries.coeff_X_pow, if_pos rfl, map_one, one_mul]
  have eval_unit : ∀ y : Submonoid.powers (PowerSeries.X : PowerSeries (GaloisField p 1)),
    IsUnit (evalPS ↑y) := by
    rintro ⟨_, k, rfl⟩
    rw [evalPS_X_pow]
    exact IsUnit.pow k (Ne.isUnit hπ_ne)
  let f : LaurentSeries (GaloisField p 1) →+* L := IsLocalization.lift eval_unit
  exact ⟨f, f.injective⟩

/--
[normAbsValQ_nontrivial](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalFields.lean)
-/
@[path]
lemma normAbsValQ_nontrivial
  [NontriviallyNormedField L_v]
  [CompleteSpace L_v]
  [Field L]
  {ι : L →+* L_v}
-- given
  (hAlg : Algebra ℚ L)
  (hFD : @FiniteDimensional ℚ L _ _ hAlg.toModule)
  (hdense : DenseRange ι) :
-- imply
  (normAbsValQ (ι.comp (algebraMap ℚ L))).IsNontrivial := by
-- proof
  by_contra h
  rw [AbsoluteValue.IsNontrivial] at h
  push Not at h
  have h_triv : ∀ q : ℚ, ‖ι ((algebraMap ℚ L) q)‖ ≤ 1 := by
    intro q
    by_cases hq : q = 0
    · simp [hq]
    · have := h q hq
      simp only [normAbsValQ, AbsoluteValue.coe_mk, MulHom.coe_mk, RingHom.coe_comp,
        Function.comp_apply] at this
      linarith
  letI := hAlg
  letI := hFD
  haveI : Fintype (Module.Free.ChooseBasisIndex ℚ L) :=
    Module.Free.ChooseBasisIndex.fintype ℚ L
  set b := Module.Free.chooseBasis ℚ L
  have hbound_L : ∀ l : L, ‖ι l‖ ≤ ∑ i, ‖ι (b i)‖ := by
    intro l
    have hl : l = ∑ i, (b.repr l i) • (b i) := (b.sum_repr l).symm
    rw [hl, map_sum]
    calc ‖∑ i, ι ((b.repr l i) • b i)‖
      ≤ ∑ i, ‖ι ((b.repr l i) • b i)‖ := norm_sum_le _ _
      _ = ∑ i, (‖ι (algebraMap ℚ L (b.repr l i))‖ * ‖ι (b i)‖) := by
        congr 1; ext i; rw [Algebra.smul_def, map_mul, norm_mul]
      _ ≤ ∑ i, (1 * ‖ι (b i)‖) := by
        apply Finset.sum_le_sum; intro i _
        exact mul_le_mul_of_nonneg_right (h_triv _) (norm_nonneg _)
      _ = ∑ i, ‖ι (b i)‖ := by simp
  set M := (∑ i, ‖ι (b i)‖) + 1
  have hbound_Lv : ∀ y : L_v, ‖y‖ ≤ M := by
    intro y
    obtain ⟨l, hl⟩ := hdense.exists_dist_lt y (show (0 : ℝ) < 1 by norm_num)
    calc ‖y‖ ≤ ‖ι l‖ + ‖y - ι l‖ := norm_le_insert' y (ι l)
      _ ≤ (∑ i, ‖ι (b i)‖) + dist y (ι l) := by
        linarith [hbound_L l, (dist_eq_norm y (ι l)).symm]
      _ ≤ (∑ i, ‖ι (b i)‖) + 1 := by linarith
  obtain ⟨x, hx⟩ := NontriviallyNormedField.non_trivial (α := L_v)
  have hx_pow : ∀ n : ℕ, ‖x‖ ^ n ≤ M := fun n => by rw [← norm_pow]; exact hbound_Lv _
  have htend := tendsto_pow_atTop_atTop_of_one_lt hx
  rw [Filter.tendsto_atTop_atTop] at htend
  obtain ⟨n, hn⟩ := htend (M + 1)
  linarith [hx_pow n, hn n le_rfl]

/--
[completion_finiteDimensional_real](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalFields.lean)
-/
@[path]
lemma completion_finiteDimensional_real
  {L_v : Type*}
  [NontriviallyNormedField L_v]
  [CompleteSpace L_v]
  {L : Type*}
  [Field L]
  {ι : L →+* L_v}
  [inst : NormedAlgebra ℝ L_v]
-- given
  (hdense : DenseRange ι)
  (hAlg : Algebra ℚ L)
  (hFD : @FiniteDimensional ℚ L _ _ hAlg.toModule)
  (_hequiv : (normAbsValQ (ι.comp (algebraMap ℚ L))).IsEquiv Rat.AbsoluteValue.real) :
-- imply
  FiniteDimensional ℝ L_v := by
-- proof
  letI : Module ℚ L := hAlg.toModule
  haveI : Module.Finite ℚ L := hFD
  set n := Module.finrank ℚ L
  set b := Module.finBasis ℚ L
  set S := Submodule.span ℝ (Set.range (fun i : Fin n => ι (b i))) with hS_def
  haveI hSfd : FiniteDimensional ℝ S :=
    Module.Finite.span_of_finite ℝ (Set.finite_range _)
  have hιL_sub : Set.range ι ⊆ (S : Set L_v) := by
    rintro y ⟨x, rfl⟩
    have hx : x = ∑ i, (b.repr x i) • (b i) := (b.sum_repr x).symm
    rw [hx, map_sum]
    apply Submodule.sum_mem
    intro i _
    rw [show (b.repr x i) • (b i) = algebraMap ℚ L (b.repr x i) * b i
      from Algebra.smul_def _ _, map_mul]
    have hcompat : ι (algebraMap ℚ L (b.repr x i)) =
      algebraMap ℝ L_v (algebraMap ℚ ℝ (b.repr x i)) := by
      have h := DFunLike.congr_fun (RingHom.ext_rat (ι.comp (algebraMap ℚ L))
        ((algebraMap ℝ L_v).comp (algebraMap ℚ ℝ))) (b.repr x i)
      exact_mod_cast h
    rw [hcompat, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hSdense : Dense (S : Set L_v) := Dense.mono hιL_sub hdense
  have hSclosed : IsClosed (S : Set L_v) := Submodule.closed_of_finiteDimensional S
  have hStop : S = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro x
    have huniv : (S : Set L_v) = Set.univ := by
      rw [← hSclosed.closure_eq, hSdense.closure_eq]
    rw [← SetLike.mem_coe, huniv]
    exact Set.mem_univ x
  have hsurj : Function.Surjective S.subtype := by
    intro x; exact ⟨⟨x, hStop ▸ Submodule.mem_top⟩, rfl⟩
  exact Module.Finite.of_surjective S.subtype hsurj
set_option maxHeartbeats 400000 in

/--
[completion_finiteDimensional_padic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalFields.lean)
-/
@[path]
lemma completion_finiteDimensional_padic
  {L_v : Type*}
  [NontriviallyNormedField L_v]
  [CompleteSpace L_v]
  {L : Type*}
  [Field L]
  {ι : L →+* L_v}
  {p : ℕ}
  [Fact (Nat.Prime p)]
  [inst : NormedAlgebra ℚ_[p] L_v]
-- given
  (hdense : DenseRange ι)
  (hAlg : Algebra ℚ L)
  (hFD : @FiniteDimensional ℚ L _ _ hAlg.toModule)
  (_hequiv : (normAbsValQ (ι.comp (algebraMap ℚ L))).IsEquiv (Rat.AbsoluteValue.padic p)) :
-- imply
  FiniteDimensional ℚ_[p] L_v := by
-- proof
  letI := hAlg; letI := hFD
  haveI : Fintype (Module.Free.ChooseBasisIndex ℚ L) :=
    Module.Free.ChooseBasisIndex.fintype ℚ L
  set b := Module.Free.chooseBasis ℚ L
  set S := Submodule.span ℚ_[p] (Set.range (fun i => ι (b i))) with hS_def
  haveI hS_fd : FiniteDimensional ℚ_[p] S :=
    FiniteDimensional.span_of_finite _ (Set.finite_range _)
  have hcompat : ∀ q : ℚ,
    (algebraMap ℚ_[p] L_v) ((algebraMap ℚ ℚ_[p]) q) = ι ((algebraMap ℚ L) q) :=
    fun q => RingHom.congr_fun (RingHom.ext_rat
      ((algebraMap ℚ_[p] L_v).comp (algebraMap ℚ ℚ_[p])) (ι.comp (algebraMap ℚ L))) q
  have hrange : Set.range ι ⊆ ↑S := by
    rintro _ ⟨l, rfl⟩
    rw [(b.sum_repr l).symm, map_sum]
    apply Submodule.sum_mem
    intro i _
    rw [Algebra.smul_def, map_mul, ← hcompat, ← Algebra.smul_def]
    exact Submodule.smul_mem S _ (Submodule.subset_span ⟨i, rfl⟩)
  have hS_closed : IsClosed (S : Set L_v) := Submodule.closed_of_finiteDimensional S
  have hS_top : S = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro x
    have hS_univ : (S : Set L_v) = Set.univ :=
      Set.eq_univ_of_univ_subset
        (hdense.closure_range ▸ hS_closed.closure_subset_iff.mpr hrange)
    rw [← SetLike.mem_coe]; rw [hS_univ]; exact Set.mem_univ x
  rw [FiniteDimensional, Module.finite_def]
  exact ⟨(Set.Finite.toFinset (Set.finite_range (fun i => ι (b i)))), by
    rw [Set.Finite.coe_toFinset]; exact hS_top⟩

/--
[properSpace_of_isCompact_closedBall_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalFields.lean)
-/
@[path]
lemma properSpace_of_isCompact_closedBall_one
  [NontriviallyNormedField K]
-- given
  (h : IsCompact (closedBall (0 : K) 1)) :
-- imply
  ProperSpace K := by
-- proof
  obtain ⟨c, hc⟩ := NontriviallyNormedField.non_trivial (α := K)
  have h_pow : ∀ n : ℕ, IsCompact (closedBall (0:K) (‖c‖^n)) := by
    intro n
    have hcn : c^n ≠ 0 := pow_ne_zero n (norm_pos_iff.mp (by linarith))
    have key : closedBall (0:K) (‖c‖^n) = (· * c^n) '' closedBall 0 1 := by
      ext y
      simp only [mem_image, mem_closedBall, dist_zero_right]
      constructor
      · intro hy
        refine ⟨y / c^n, ?_, ?_⟩
        · rw [norm_div, norm_pow]
          exact div_le_one_of_le₀ hy (pow_nonneg (norm_nonneg c) n)
        · field_simp
      · rintro ⟨x, hx, rfl⟩
        rw [norm_mul, norm_pow]
        nlinarith [pow_nonneg (norm_nonneg c) n]
    rw [key]
    exact IsCompact.image h (continuous_mul_const (c^n))
  apply ProperSpace.mk
  intro x r
  by_cases hr : r < 0
  · simp [closedBall_eq_empty.mpr hr]
  push Not at hr
  have hsub : closedBall x r ⊆ closedBall (0:K) (‖x‖ + r) := by
    intro y hy
    simp only [mem_closedBall, dist_zero_right] at *
    linarith [norm_sub_norm_le y x, show ‖y - x‖ ≤ r from by rwa [← dist_eq_norm]]
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ‖x‖ + r ≤ ‖c‖^N := by
    have := tendsto_pow_atTop_atTop_of_one_lt hc
    rw [tendsto_atTop_atTop] at this
    obtain ⟨N, hN⟩ := this (‖x‖ + r)
    exact ⟨N, hN N le_rfl⟩
  exact (h_pow N).of_isClosed_subset isClosed_closedBall
    (hsub.trans (closedBall_subset_closedBall hN))

/--
[normAbsValQ_equiv_real_implies_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalFields.lean)
-/
@[path]
lemma normAbsValQ_equiv_real_implies_eq
  [NontriviallyNormedField L_v]
  [CompleteSpace L_v]
  {j : ℚ →+* L_v}
-- given
  (hequiv : (normAbsValQ j).IsEquiv Rat.AbsoluteValue.real)
  (hnorm_2 : ‖j (2 : ℚ)‖ = 2) :
-- imply
  normAbsValQ j = Rat.AbsoluteValue.real :=
-- proof
  normAbsValQ_isEquiv_real_eq j hequiv hnorm_2

/--
[not_accPt_of_separated](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalFields.lean)
-/
@[path]
private lemma not_accPt_of_separated_eq
  [MetricSpace X]
  {S : Set X}
  {a : X}
-- given
  (h_sep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ dist x y) :
-- imply
  ¬ AccPt a (𝓟 S) := by
-- proof
  apply not_accPt_of_separated h_sep a

/--
[absValFromNorm_isNontrivial](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalFields.lean)
-/
@[path]
private lemma absValFromNorm_isNontrivial_eq
  {L : Type*}
  [IsLocalField L]
  [CharZero L] :
-- imply
  (absValFromNorm L).IsNontrivial := by
-- proof
  apply absValFromNorm_isNontrivial L

/--
[absValFromNorm_eq_normAbsValQ_castHom](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalFields.lean)
-/
@[path]
private lemma absValFromNorm_eq_normAbsValQ_castHom_eq
  {L : Type*}
  [NontriviallyNormedField L]
  [CharZero L] :
-- imply
  absValFromNorm L = normAbsValQ (Rat.castHom L) := by
-- proof
  apply absValFromNorm_eq_normAbsValQ_castHom L

/--
[normAbsValQ_isEquiv_real_uniformContinuous](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalFields.lean)
-/
@[path]
private lemma normAbsValQ_isEquiv_real_uniformContinuous_eq
  [NontriviallyNormedField L_v]
  {j : ℚ →+* L_v}
-- given
  (hequiv : (normAbsValQ j).IsEquiv Rat.AbsoluteValue.real) :
-- imply
  UniformContinuous j := by
-- proof
  apply normAbsValQ_isEquiv_real_uniformContinuous j hequiv

/--
[extendRingHom_real_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalFields.lean)
-/
@[path]
private lemma extendRingHom_real_continuous_eq
  [NontriviallyNormedField L_v]
  [CompleteSpace L_v]
  {j : ℚ →+* L_v}
-- given
  (hequiv : (normAbsValQ j).IsEquiv Rat.AbsoluteValue.real) :
-- imply
  Continuous (extendRingHom_real j hequiv) := by
-- proof
  apply extendRingHom_real_continuous j hequiv

/--
[extendRingHom_real_extends](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalFields.lean)
-/
@[path]
private lemma extendRingHom_real_extends_eq
  [NontriviallyNormedField L_v]
  [CompleteSpace L_v]
  {j : ℚ →+* L_v}
  {q : ℚ}
-- given
  (hequiv : (normAbsValQ j).IsEquiv Rat.AbsoluteValue.real) :
-- imply
  extendRingHom_real j hequiv (q : ℝ) = j q := by
-- proof
  apply extendRingHom_real_extends j hequiv q

/--
[normAbsValQ_isEquiv_padic_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalFields.lean)
-/
@[path]
private lemma normAbsValQ_isEquiv_padic_eq_eq
  [NontriviallyNormedField L_v]
  [CompleteSpace L_v]
  {j : ℚ →+* L_v}
  {p : ℕ}
  [Fact (Nat.Prime p)]
-- given
  (hequiv : (normAbsValQ j).IsEquiv (Rat.AbsoluteValue.padic p))
  (hnorm_p : ‖j (↑p : ℚ)‖ = (↑p : ℝ)⁻¹) :
-- imply
  normAbsValQ j = Rat.AbsoluteValue.padic p := by
-- proof
  apply normAbsValQ_isEquiv_padic_eq j p hequiv hnorm_p

/--
[j_comp_equiv_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalFields.lean)
-/
@[path]
private lemma j_comp_equiv_continuous_eq
  [NontriviallyNormedField L_v]
  [CompleteSpace L_v]
  {j : ℚ →+* L_v}
  {p : ℕ}
  [Fact (Nat.Prime p)]
-- given
  (heq : normAbsValQ j = Rat.AbsoluteValue.padic p) :
-- imply
  Continuous (j.comp (WithVal.equiv (Rat.padicValuation p)).toRingHom) := by
-- proof
  apply j_comp_equiv_continuous j p heq

/--
[extendRingHom_padic_on_rat](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalFields.lean)
-/
@[path]
private lemma extendRingHom_padic_on_rat_eq
  [NontriviallyNormedField L_v]
  [CompleteSpace L_v]
  {j : ℚ →+* L_v}
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {q : ℚ}
-- given
  (heq : normAbsValQ j = Rat.AbsoluteValue.padic p) :
-- imply
  extendRingHom_padic j p heq (q : ℚ_[p]) = j q := by
-- proof
  apply extendRingHom_padic_on_rat j p heq q

/--
[extendRingHom_padic_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalFields.lean)
-/
@[path]
private lemma extendRingHom_padic_continuous_eq
  [NontriviallyNormedField L_v]
  [CompleteSpace L_v]
  {j : ℚ →+* L_v}
  {p : ℕ}
  [Fact (Nat.Prime p)]
-- given
  (heq : normAbsValQ j = Rat.AbsoluteValue.padic p) :
-- imply
  Continuous (extendRingHom_padic j p heq) := by
-- proof
  apply extendRingHom_padic_continuous j p heq

/--
[extendRingHom_padic_isometry](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalFields.lean)
-/
@[path]
private lemma extendRingHom_padic_isometry_eq
  [NontriviallyNormedField L_v]
  [CompleteSpace L_v]
  {j : ℚ →+* L_v}
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {x : ℚ_[p]}
-- given
  (heq : normAbsValQ j = Rat.AbsoluteValue.padic p) :
-- imply
  ‖extendRingHom_padic j p heq x‖ = ‖x‖ := by
-- proof
  apply extendRingHom_padic_isometry j p heq x

/--
[normAbsValQ_isEquiv_real_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalFields.lean)
-/
@[path]
private lemma normAbsValQ_isEquiv_real_eq_eq
  [NontriviallyNormedField L_v]
  [CompleteSpace L_v]
  {j : ℚ →+* L_v}
-- given
  (hequiv : (normAbsValQ j).IsEquiv Rat.AbsoluteValue.real)
  (hnorm_2 : ‖j (2 : ℚ)‖ = 2) :
-- imply
  normAbsValQ j = Rat.AbsoluteValue.real := by
-- proof
  apply normAbsValQ_isEquiv_real_eq j hequiv hnorm_2

/--
[j_comp_equiv_continuous_of_equiv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalFields.lean)
-/
@[path]
private lemma j_comp_equiv_continuous_of_equiv_eq
  [NontriviallyNormedField L_v]
  [CompleteSpace L_v]
  {j : ℚ →+* L_v}
  {p : ℕ}
  [Fact (Nat.Prime p)]
-- given
  (hequiv : (normAbsValQ j).IsEquiv (Rat.AbsoluteValue.padic p)) :
-- imply
  Continuous (j.comp (WithVal.equiv (Rat.padicValuation p)).toRingHom) := by
-- proof
  apply j_comp_equiv_continuous_of_equiv j p hequiv

/--
[extendRingHom_padic_of_equiv_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalFields.lean)
-/
@[path]
private lemma extendRingHom_padic_of_equiv_continuous_eq
  [NontriviallyNormedField L_v]
  [CompleteSpace L_v]
  {j : ℚ →+* L_v}
  {p : ℕ}
  [Fact (Nat.Prime p)]
-- given
  (hequiv : (normAbsValQ j).IsEquiv (Rat.AbsoluteValue.padic p)) :
-- imply
  Continuous (extendRingHom_padic_of_equiv j p hequiv) := by
-- proof
  apply extendRingHom_padic_of_equiv_continuous j p hequiv


-- created on 2026-10-23
