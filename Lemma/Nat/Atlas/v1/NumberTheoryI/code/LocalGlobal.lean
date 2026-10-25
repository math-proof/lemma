import Mathlib
import sympy.Basic
import Abbrev.v1.Atlas.NumberTheoryI.code.LocalGlobal
open NumberField IsDedekindDomain Polynomial Finset in IntermediateField
open scoped NumberField TensorProduct


/--
[finrank_le_two_of_isReal_place](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalGlobal.lean)
-/
@[path]
lemma finrank_le_two_of_isReal_place
  {K : Type}
  [Field K]
  [NumberField K]
  {v : InfinitePlace K}
  {M : Type*}
  [Field M]
  [Algebra (InfinitePlace.Completion v) M]
  [FiniteDimensional (InfinitePlace.Completion v) M]
-- given
  (hv : InfinitePlace.IsReal v) :
-- imply
  Module.finrank (InfinitePlace.Completion v) M ≤ 2 := by
-- proof
  let e := InfinitePlace.Completion.ringEquivRealOfIsReal hv
  letI : Algebra ℝ M :=
    RingHom.toAlgebra ((algebraMap (InfinitePlace.Completion v) M).comp e.symm.toRingHom)
  have hcompat : (algebraMap ℝ M).comp e.toRingHom =
    (RingEquiv.refl M).toRingHom.comp (algebraMap (InfinitePlace.Completion v) M) := by
    ext x
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.refl_apply,
      RingHom.coe_coe]
    show (algebraMap v.Completion M) (e.symm (e x)) = algebraMap v.Completion M x
    rw [e.symm_apply_apply]
  haveI : Module.Finite ℝ M := Module.Finite.of_equiv_equiv e (RingEquiv.refl M) hcompat
  haveI : Algebra.IsAlgebraic ℝ M := Algebra.IsAlgebraic.of_finite ℝ M
  have hfr : Module.finrank (InfinitePlace.Completion v) M = Module.finrank ℝ M :=
    Algebra.finrank_eq_of_equiv_equiv e (RingEquiv.refl M) hcompat
  rw [hfr]
  obtain ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩ := Real.nonempty_algEquiv_or M
  ·
    have : Module.finrank ℝ M = Module.finrank ℝ ℝ := f.toLinearEquiv.finrank_eq
    rw [this, Module.finrank_self]; omega
  ·
    have : Module.finrank ℝ M = Module.finrank ℝ ℂ := f.toLinearEquiv.finrank_eq
    rw [this, Complex.finrank_real_complex]

/--
[exists_degree_two_extension_above_real_place](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalGlobal.lean)
-/
@[path]
lemma exists_degree_two_extension_above_real_place
  {K : Type}
  [Field K]
  [NumberField K]
  {v : InfinitePlace K}
  {M : Type*}
  [Field M]
  [Algebra (InfinitePlace.Completion v) M]
  [FiniteDimensional (InfinitePlace.Completion v) M]
  [Algebra.IsSeparable (InfinitePlace.Completion v) M]
-- given
  (hv : InfinitePlace.IsReal v)
  (hfin : Module.finrank (InfinitePlace.Completion v) M = 2) :
-- imply
  ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L) (_ : Algebra.IsSeparable K L) (_ : FiniteDimensional K L) (w : InfinitePlace L) (_ : w.comap (algebraMap K L) = v), Module.finrank K L = 2 ∧ ∃ (_ : Algebra (InfinitePlace.Completion v) (InfinitePlace.Completion w)), Nonempty (@AlgEquiv (InfinitePlace.Completion v) M (InfinitePlace.Completion w) _ _ _ _ ‹_›) := by
-- proof
  let e_real := InfinitePlace.Completion.ringEquivRealOfIsReal hv
  let φ_real : K →+* ℝ := e_real.toRingHom.comp (algebraMap K (InfinitePlace.Completion v))
  set f := (Polynomial.X : Polynomial K)^2 + 1 with hf_def
  have h_eq_XC : f = Polynomial.X^2 + Polynomial.C 1 := by simp [hf_def]
  have hne : (Polynomial.X^2 + Polynomial.C (1 : K)) ≠ 0 :=
    (Polynomial.monic_X_pow_add_C (1 : K) two_ne_zero).ne_zero
  have hmonic : Polynomial.Monic f := by
    rw [h_eq_XC]; exact Polynomial.monic_X_pow_add_C 1 two_ne_zero
  have hirr : Irreducible f := by
    rw [show Irreducible f ↔ f.roots = 0 from
      Polynomial.Monic.irreducible_iff_roots_eq_zero_of_degree_le_three hmonic
        (by rw [h_eq_XC, Polynomial.natDegree_X_pow_add_C])
        (by rw [h_eq_XC, Polynomial.natDegree_X_pow_add_C]; omega)]
    rw [Multiset.eq_zero_iff_forall_notMem]
    intro a ha
    rw [Polynomial.mem_roots (by rw [h_eq_XC]; exact hne)] at ha
    have heval : a ^ 2 + 1 = (0 : K) := by
      rw [Polynomial.IsRoot.def] at ha
      simpa [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_one, hf_def] using ha
    have := congr_arg φ_real heval
    simp at this
    linarith [sq_nonneg (φ_real a)]
  haveI : Fact (Irreducible f) := ⟨hirr⟩
  haveI : CharZero (AdjoinRoot f) :=
    charZero_of_injective_algebraMap (algebraMap K (AdjoinRoot f)).injective
  haveI : Module.Finite K (AdjoinRoot f) :=
    (AdjoinRoot.powerBasis hirr.ne_zero).finite
  haveI : Module.Finite ℚ (AdjoinRoot f) := Module.Finite.trans K (AdjoinRoot f)
  haveI : NumberField (AdjoinRoot f) := NumberField.mk
  haveI : FiniteDimensional K (AdjoinRoot f) := inferInstance
  haveI : Algebra.IsIntegral K (AdjoinRoot f) := Algebra.IsIntegral.of_finite K (AdjoinRoot f)
  haveI : Algebra.IsSeparable K (AdjoinRoot f) :=
    Algebra.IsSeparable.of_integral K (AdjoinRoot f)
  let ψ : AdjoinRoot f →+* ℂ :=
    AdjoinRoot.lift v.embedding Complex.I (by
      simp [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_one, Complex.I_sq, hf_def])
  let w : InfinitePlace (AdjoinRoot f) := InfinitePlace.mk ψ
  have hcomap : w.comap (algebraMap K (AdjoinRoot f)) = v := by
    show (InfinitePlace.mk ψ).comap (algebraMap K (AdjoinRoot f)) = v
    rw [InfinitePlace.comap_mk]
    have : ψ.comp (algebraMap K (AdjoinRoot f)) = v.embedding := by
      ext x; simp [ψ, AdjoinRoot.algebraMap_eq]
    rw [this, InfinitePlace.mk_embedding]
  have hfinrank : Module.finrank K (AdjoinRoot f) = 2 := by
    rw [(AdjoinRoot.powerBasis hirr.ne_zero).finrank]
    show f.natDegree = 2
    conv_lhs => rw [h_eq_XC]
    exact Polynomial.natDegree_X_pow_add_C
  have hw_complex : w.IsComplex := by
    rw [InfinitePlace.not_isReal_iff_isComplex.symm, InfinitePlace.isReal_mk_iff,
      NumberField.ComplexEmbedding.isReal_iff]
    intro hreal
    have h1 := congr_fun (congr_arg DFunLike.coe hreal) (AdjoinRoot.root f)
    simp only [NumberField.ComplexEmbedding.conjugate_coe_eq] at h1
    rw [AdjoinRoot.lift_root,
      show (starRingEnd ℂ) Complex.I = -Complex.I from by simp [Complex.conj_I]] at h1
    have h3 : -Complex.I + Complex.I = Complex.I + Complex.I := congr_arg (· + Complex.I) h1
    rw [neg_add_cancel] at h3
    have := mul_eq_zero.mp (show (2 : ℂ) * Complex.I = 0 by rw [two_mul]; exact h3.symm)
    exact Complex.I_ne_zero (this.resolve_left (by norm_num))
  let e_w := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw_complex
  let alg_vw : Algebra v.Completion w.Completion :=
    RingHom.toAlgebra (e_w.symm.toRingHom.comp ((algebraMap ℝ ℂ).comp e_real.toRingHom))
  letI alg_RM : Algebra ℝ M :=
    RingHom.toAlgebra ((algebraMap v.Completion M).comp e_real.symm.toRingHom)
  letI alg_RW : Algebra ℝ w.Completion :=
    RingHom.toAlgebra (e_w.symm.toRingHom.comp (algebraMap ℝ ℂ))
  have hcompat_M : (algebraMap ℝ M).comp e_real.toRingHom =
    (RingEquiv.refl M).toRingHom.comp (algebraMap v.Completion M) := by
    ext x
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.refl_apply,
      RingHom.coe_coe]
    show (algebraMap v.Completion M) (e_real.symm (e_real x)) = algebraMap v.Completion M x
    rw [e_real.symm_apply_apply]
  haveI : Module.Finite ℝ M := Module.Finite.of_equiv_equiv e_real (RingEquiv.refl M) hcompat_M
  haveI : Algebra.IsAlgebraic ℝ M := Algebra.IsAlgebraic.of_finite ℝ M
  have hfr : Module.finrank ℝ M = 2 := by
    rw [← hfin]
    exact (Algebra.finrank_eq_of_equiv_equiv e_real (RingEquiv.refl M) hcompat_M).symm
  refine ⟨AdjoinRoot f, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, w, hcomap, hfinrank, alg_vw, ?_⟩
  obtain ⟨⟨fR⟩⟩ | ⟨⟨fC⟩⟩ := Real.nonempty_algEquiv_or M
  ·
    exfalso
    have := fR.toLinearEquiv.finrank_eq
    rw [hfr, Module.finrank_self] at this; omega
  ·
    let ew_alg : ℂ ≃ₐ[ℝ] w.Completion := AlgEquiv.ofRingEquiv (f := e_w.symm) (fun _ => rfl)
    let f_RMW : M ≃ₐ[ℝ] w.Completion := fC.trans ew_alg
    have hf_compat : ∀ x : v.Completion,
      f_RMW.toRingEquiv ((algebraMap v.Completion M) x) =
      @algebraMap v.Completion w.Completion _ _ alg_vw x := by
      intro x
      have h1 : (algebraMap v.Completion M) x = @algebraMap ℝ M _ _ alg_RM (e_real x) := by
        show (algebraMap v.Completion M) x =
          (algebraMap v.Completion M) (e_real.symm (e_real x))
        rw [e_real.symm_apply_apply]
      rw [h1]
      show f_RMW (@algebraMap ℝ M _ _ alg_RM (e_real x)) =
        @algebraMap v.Completion w.Completion _ _ alg_vw x
      rw [f_RMW.commutes]
      rfl
    exact ⟨AlgEquiv.ofRingEquiv (f := f_RMW.toRingEquiv) hf_compat⟩

/--
[finrank_eq_one_of_isAlgClosed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalGlobal.lean)
-/
@[path]
lemma finrank_eq_one_of_isAlgClosed
  {F E : Type*}
  [Field F]
  [Field E]
  [Algebra F E]
  [IsAlgClosed F]
  [FiniteDimensional F E] :
-- imply
  Module.finrank F E = 1 := by
-- proof
  have hsurj : Function.Surjective (algebraMap F E) := fun x =>
    minpoly.mem_range_of_degree_eq_one _ x
      (IsAlgClosed.degree_eq_one_of_irreducible _
        (minpoly.irreducible (Algebra.IsIntegral.isIntegral x)))
  have hle : F ≃ₗ[F] E := LinearEquiv.ofBijective (Algebra.linearMap _ E)
    ⟨(algebraMap F E).injective, hsurj⟩
  rw [← Module.finrank_self (R := F)]; exact hle.finrank_eq.symm

/--
[exists_heightOneSpectrum_above](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalGlobal.lean)
-/
@[path]
lemma exists_heightOneSpectrum_above
  [Field K]
  [Field L]
  [NumberField K]
  [NumberField L]
  [Algebra K L]
  {v : HeightOneSpectrum (𝓞 K)} :
-- imply
  ∃ w : HeightOneSpectrum (𝓞 L), w.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L)) = v.asIdeal := by
-- proof
  obtain ⟨Q, _, hQ_prime, hQ_comap⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral v.asIdeal (⊥ : Ideal (𝓞 L)) (by simp)
  have hQ_ne : Q ≠ ⊥ := by
    intro h; rw [h] at hQ_comap; simp at hQ_comap; exact v.ne_bot hQ_comap.symm
  exact ⟨⟨Q, hQ_prime, hQ_ne⟩, hQ_comap⟩

/--
[exists_monic_approx_poly](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalGlobal.lean)
-/
@[path]
lemma exists_monic_approx_poly
  [Field K]
  [NontriviallyNormedField K_v]
  [Algebra K K_v]
  {f : Polynomial K_v}
  {δ : ℝ}
-- given
  (hdense : DenseRange (algebraMap K K_v))
  (hf_monic : f.Monic)
  (hf_deg : 0 < f.natDegree)
  (hδ : 0 < δ) :
-- imply
  ∃ g : Polynomial K, g.Monic ∧ g.natDegree = f.natDegree ∧ Polynomial.L1norm (normAbsVal K_v) (f - g.map (algebraMap K K_v)) < δ := by
-- proof
  classical
  set n := f.natDegree with hn_def
  set ε := δ / (↑n + 1)
  have hε : (0 : ℝ) < ε := div_pos hδ (by positivity)
  have hn1 : (0 : ℝ) < ↑n + 1 := by positivity
  choose b hb using fun i : Fin n => hdense.exists_dist_lt (f.coeff i) hε
  set g : Polynomial K := X ^ n + ∑ i : Fin n, C (b i) * X ^ (i : ℕ)
  have hdeg_low : (∑ i : Fin n, C (b i) * X ^ (i : ℕ) : Polynomial K).degree < ↑n := by
    apply lt_of_le_of_lt (degree_sum_le _ _)
    apply (Finset.sup_lt_iff _).mpr
    · intro i _; exact lt_of_le_of_lt (degree_C_mul_X_pow_le _ _) (by exact_mod_cast i.isLt)
    · exact WithBot.bot_lt_coe n
  have hg_monic : g.Monic := monic_X_pow_add hdeg_low
  have hg_natdeg : g.natDegree = n := by
    have : (∑ i : Fin n, C (b i) * X ^ (i : ℕ) : Polynomial K).degree <
      (X ^ n : Polynomial K).degree := by rwa [degree_X_pow]
    simp only [g, natDegree_add_eq_left_of_degree_lt this, natDegree_X_pow]
  refine ⟨g, hg_monic, hg_natdeg, ?_⟩
  set p := f - g.map (algebraMap K K_v)
  have hsupp : p.support ⊆ Finset.range n := by
    intro i hi
    rw [Finset.mem_range]; by_contra h; push Not at h
    rw [mem_support_iff] at hi; apply hi
    show (f - g.map (algebraMap K K_v)).coeff i = 0
    rw [coeff_sub, coeff_map]
    obtain rfl | hlt := eq_or_lt_of_le h
    · rw [hf_monic.coeff_natDegree, show g.coeff n = 1 from hg_natdeg ▸ hg_monic.coeff_natDegree,
      map_one, sub_self]
    · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega), map_zero, sub_self]
  have hL1 : Polynomial.L1norm (normAbsVal K_v) p =
    ∑ i ∈ Finset.range n, normAbsVal K_v (p.coeff i) :=
    Finset.sum_subset hsupp (fun i _ hi => by
      rw [mem_support_iff, not_not] at hi; rw [hi, map_zero])
  have hg_coeff : ∀ i (hi : i < n), g.coeff i = b ⟨i, hi⟩ := by
    intro i hi
    simp only [g, coeff_add, coeff_X_pow, finset_sum_coeff, coeff_C_mul_X_pow,
      if_neg (Nat.ne_of_lt hi), zero_add]
    rw [Finset.sum_eq_single ⟨i, hi⟩]
    · simp
    · intro j _ hj
      simp [show i ≠ (j : ℕ) from fun h => hj (Fin.ext (h ▸ rfl))]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hcoeff : ∀ i (hi : i < n),
    p.coeff i = f.coeff i - algebraMap K K_v (b ⟨i, hi⟩) := by
    intro i hi
    show (f - g.map (algebraMap K K_v)).coeff i = _
    rw [coeff_sub, coeff_map, hg_coeff i hi]
  rw [hL1]
  calc ∑ i ∈ Finset.range n, normAbsVal K_v (p.coeff i)
    < ∑ _ ∈ Finset.range n, ε := by
      apply Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.mpr (by omega))
      intro i hi; rw [Finset.mem_range] at hi
      rw [hcoeff i hi]
      show ‖f.coeff i - algebraMap K K_v (b ⟨i, hi⟩)‖ < ε
      rw [← dist_eq_norm]; exact hb ⟨i, hi⟩
    _ = ↑n * ε := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ < δ := by
      calc ↑n * (δ / (↑n + 1)) = δ * (↑n / (↑n + 1)) := by ring
        _ < δ * 1 := by
          apply mul_lt_mul_of_pos_left _ hδ
          rw [div_lt_one hn1]; linarith
        _ = δ := mul_one δ

/--
[krasner_irreducible](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalGlobal.lean)
-/
@[path]
lemma krasner_irreducible
  [NontriviallyNormedField K_v]
  [IsUltrametricDist K_v]
  [CompleteSpace K_v]
  {f g : Polynomial K_v}
-- given
  (hf_monic : f.Monic)
  (hf_irr : Irreducible f)
  (hf_sep : f.Separable)
  (hg_monic : g.Monic)
  (hg_deg : g.natDegree = f.natDegree)
  (hclose : ∃ δ : ℝ, 0 < δ ∧ Polynomial.L1norm (normAbsVal K_v) (f - g) < δ ∧ ∀ g' : Polynomial K_v, g'.Monic → g'.natDegree = f.natDegree → Polynomial.L1norm (normAbsVal K_v) (f - g') < δ → ∀ β : AlgebraicClosure K_v, Polynomial.aeval β g' = 0 → ∃ α : AlgebraicClosure K_v, Polynomial.aeval α f = 0 ∧ IntermediateField.adjoin K_v {α} = IntermediateField.adjoin K_v {β}) :
-- imply
  Irreducible g := by
-- proof
  obtain ⟨δ, _, hfg_close, hδ_approx⟩ := hclose
  have hg_deg_pos : 0 < g.natDegree := hg_deg ▸ hf_irr.natDegree_pos
  have hg_deg_ne : g.degree ≠ 0 :=
    ne_of_gt (Polynomial.natDegree_pos_iff_degree_pos.mp hg_deg_pos)
  obtain ⟨β, hβ⟩ :=
    IsAlgClosed.exists_aeval_eq_zero (AlgebraicClosure K_v) g hg_deg_ne
  obtain ⟨α, hα_root, hfield_eq⟩ :=
    hδ_approx g hg_monic hg_deg hfg_close β hβ
  have hα_int : IsIntegral K_v α := (Algebra.IsAlgebraic.isAlgebraic α).isIntegral
  have hmin_α_eq_f : minpoly K_v α = f := by
    have hmin_dvd : minpoly K_v α ∣ f := minpoly.dvd K_v α hα_root
    exact Polynomial.eq_of_monic_of_associated (minpoly.monic hα_int) hf_monic
      ((minpoly.irreducible hα_int).associated_of_dvd hf_irr hmin_dvd)
  have hβ_int : IsIntegral K_v β := (Algebra.IsAlgebraic.isAlgebraic β).isIntegral
  have hmin_dvd_g : minpoly K_v β ∣ g := minpoly.dvd K_v β hβ
  open IntermediateField in
  have hfinrank_eq : Module.finrank K_v K_v⟮α⟯ = Module.finrank K_v K_v⟮β⟯ := by
    have : K_v⟮α⟯.toSubalgebra = K_v⟮β⟯.toSubalgebra := congrArg toSubalgebra hfield_eq
    exact LinearEquiv.finrank_eq (Subalgebra.equivOfEq _ _ this).toLinearEquiv
  open IntermediateField in
  have hdeg_min_β : (minpoly K_v β).natDegree = f.natDegree := by
    have h1 := adjoin.finrank hα_int
    have h2 := adjoin.finrank hβ_int
    rw [hmin_α_eq_f] at h1
    omega
  have hg_eq : g = minpoly K_v β :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hβ_int) hg_monic
      hmin_dvd_g (by omega)
  rw [hg_eq]
  exact minpoly.irreducible hβ_int

/--
[algEquiv_adjoinRoot_of_root](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalGlobal.lean)
-/
@[path]
lemma algEquiv_adjoinRoot_of_root
  {F : Type*}
  [Field F]
  {g : Polynomial F}
  {M : Type*}
  [Field M]
  [Algebra F M]
  [FiniteDimensional F M]
  {α : M}
-- given
  (hg_irr : Irreducible g)
  (hg_monic : g.Monic)
  (hM_deg : Module.finrank F M = g.natDegree)
  (hα : Polynomial.aeval α g = 0) :
-- imply
  Nonempty (M ≃ₐ[F] AdjoinRoot g) := by
-- proof
  haveI : Fact (Irreducible g) := ⟨hg_irr⟩
  have hα' : Polynomial.eval₂ (algebraMap F M) α g = 0 := by
    rwa [Polynomial.aeval_def] at hα
  let hlift : AdjoinRoot g →ₐ[F] M := AdjoinRoot.liftAlgHom g (Algebra.ofId F M) α hα'
  have hinj : Function.Injective hlift := RingHom.injective hlift.toRingHom
  have hfr : Module.finrank F (AdjoinRoot g) = g.natDegree := by
    rw [(AdjoinRoot.powerBasis' hg_monic).finrank]; rfl
  haveI : FiniteDimensional F (AdjoinRoot g) :=
    Module.finite_of_finrank_pos (by rw [hfr]; exact Irreducible.natDegree_pos hg_irr)
  have hdim : Module.finrank F (AdjoinRoot g) = Module.finrank F M := by
    rw [hfr, hM_deg]
  have hsurj : Function.Surjective hlift :=
    (hlift.toLinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  exact ⟨(AlgEquiv.ofBijective hlift ⟨hinj, hsurj⟩).symm⟩

/--
[adjoinRoot_equiv_of_intermediateField_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalGlobal.lean)
-/
@[path]
lemma adjoinRoot_equiv_of_intermediateField_eq
  {K : Type*}
  [Field K]
  {E : Type*}
  [Field E]
  [Algebra K E]
  {p q : Polynomial K}
  {α β : E}
-- given
  (hp_irr : Irreducible p)
  (hp_monic : p.Monic)
  (hq_irr : Irreducible q)
  (hq_monic : q.Monic)
  (hα : Polynomial.aeval α p = 0)
  (hβ : Polynomial.aeval β q = 0)
  (heq : IntermediateField.adjoin K {α} = IntermediateField.adjoin K {β}) :
-- imply
  Nonempty (AdjoinRoot p ≃ₐ[K] AdjoinRoot q) := by
-- proof
  have hα_int : IsIntegral K α := ⟨p, hp_monic, hα⟩
  have hβ_int : IsIntegral K β := ⟨q, hq_monic, hβ⟩
  have hminα : minpoly K α = p :=
    (minpoly.eq_of_irreducible_of_monic hp_irr hα hp_monic).symm
  have hminβ : minpoly K β = q :=
    (minpoly.eq_of_irreducible_of_monic hq_irr hβ hq_monic).symm
  have e1 : AdjoinRoot p ≃ₐ[K] ↥(IntermediateField.adjoin K {α}) := by
    rw [← hminα]; exact IntermediateField.adjoinRootEquivAdjoin K hα_int
  have e2 : ↥(IntermediateField.adjoin K {α}) ≃ₐ[K] ↥(IntermediateField.adjoin K {β}) :=
    IntermediateField.equivOfEq heq
  have e3 : ↥(IntermediateField.adjoin K {β}) ≃ₐ[K] AdjoinRoot q := by
    rw [← hminβ]; exact (IntermediateField.adjoinRootEquivAdjoin K hβ_int).symm
  exact ⟨e1.trans (e2.trans e3)⟩

/--
[separableExtension_isCompletion_infinitePlace](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalGlobal.lean)
-/
@[path]
lemma separableExtension_isCompletion_infinitePlace
  {K : Type}
  [Field K]
  [NumberField K]
  {v : InfinitePlace K}
  {M : Type*}
  [Field M]
  [Algebra (InfinitePlace.Completion v) M]
  [FiniteDimensional (InfinitePlace.Completion v) M]
  [Algebra.IsSeparable (InfinitePlace.Completion v) M] :
-- imply
  ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L) (_ : Algebra.IsSeparable K L) (_ : FiniteDimensional K L) (w : InfinitePlace L) (_ : w.comap (algebraMap K L) = v), Module.finrank K L = Module.finrank (InfinitePlace.Completion v) M ∧ ∃ (_ : Algebra (InfinitePlace.Completion v) (InfinitePlace.Completion w)), Nonempty (@AlgEquiv (InfinitePlace.Completion v) M (InfinitePlace.Completion w) _ _ _ _ ‹_›) := by
-- proof
  obtain hv | hv := InfinitePlace.isReal_or_isComplex v
  ·
    have hle := finrank_le_two_of_isReal_place hv M
    have hpos : 0 < Module.finrank (InfinitePlace.Completion v) M := Module.finrank_pos
    by_cases h1 : Module.finrank (InfinitePlace.Completion v) M = 1
    ·
      refine ⟨K, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
        v, rfl, ?_, inferInstance, ?_⟩
      · rw [h1]; exact Module.finrank_self K
      · exact ⟨algEquivOfFinrankOne _ _ h1⟩
    ·
      have h2 : Module.finrank (InfinitePlace.Completion v) M = 2 := by omega
      obtain ⟨L, hL1, hL2, hL3, hL4, hL5, w, hw, hfin, halg, hiso⟩ :=
        exists_degree_two_extension_above_real_place v hv M h2
      exact ⟨L, hL1, hL2, hL3, hL4, hL5, w, hw, by rw [hfin, h2], halg, hiso⟩
  ·
    haveI : IsAlgClosed (InfinitePlace.Completion v) :=
      IsAlgClosed.of_ringEquiv _ _
        (InfinitePlace.Completion.ringEquivComplexOfIsComplex hv).symm
    have h1 := finrank_eq_one_of_isAlgClosed (InfinitePlace.Completion v) M
    refine ⟨K, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      v, rfl, ?_, inferInstance, ?_⟩
    · rw [h1]; exact Module.finrank_self K
    · exact ⟨algEquivOfFinrankOne _ _ h1⟩

/--
[galoisExtension_isCompletion_infinitePlace](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalGlobal.lean)
-/
@[path]
lemma galoisExtension_isCompletion_infinitePlace
  {K : Type}
  [Field K]
  [NumberField K]
  {v : InfinitePlace K}
  {M : Type*}
  [Field M]
  [Algebra (InfinitePlace.Completion v) M]
  [FiniteDimensional (InfinitePlace.Completion v) M]
  [IsGalois (InfinitePlace.Completion v) M] :
-- imply
  ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L) (_ : IsGalois K L) (_ : FiniteDimensional K L) (w : InfinitePlace L) (_ : w.comap (algebraMap K L) = v), (∃ (_ : Algebra (InfinitePlace.Completion v) (InfinitePlace.Completion w)), Nonempty (@AlgEquiv (InfinitePlace.Completion v) M (InfinitePlace.Completion w) _ _ _ _ ‹_›)) ∧ Nonempty (MulEquiv (L ≃ₐ[K] L) (M ≃ₐ[InfinitePlace.Completion v] M)) := by
-- proof
  obtain hv | hv := InfinitePlace.isReal_or_isComplex v
  ·
    have hle := finrank_le_two_of_isReal_place hv M
    have hpos : 0 < Module.finrank (InfinitePlace.Completion v) M := Module.finrank_pos
    by_cases h1 : Module.finrank (InfinitePlace.Completion v) M = 1
    ·
      refine ⟨K, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
        v, rfl, ?_, ?_⟩
      · exact ⟨inferInstance, ⟨algEquivOfFinrankOne _ _ h1⟩⟩
      · exact ⟨galoisGroupMulEquivTrivial K _ _ h1⟩
    ·
      have h2 : Module.finrank (InfinitePlace.Completion v) M = 2 := by omega
      haveI : Algebra.IsSeparable (InfinitePlace.Completion v) M := inferInstance
      obtain ⟨L, hFL, hNF, hAlg, hSep, hFD, w, hw, hfin, halg, hiso⟩ :=
        exists_degree_two_extension_above_real_place v hv M h2
      letI := hFL; letI := hNF; letI := hAlg; letI := hSep; letI := hFD
      haveI : Algebra.IsQuadraticExtension K L := ⟨hfin⟩
      haveI : IsGalois K L := inferInstance
      refine ⟨L, hFL, hNF, hAlg, inferInstance, hFD, w, hw, ?_, ?_⟩
      · exact ⟨halg, hiso⟩
      · haveI : Fact (Nat.Prime 2) := Fact.mk (by decide)
        exact ⟨mulEquivOfPrimeCardEq
          ((IsGalois.card_aut_eq_finrank K L).trans hfin)
          ((IsGalois.card_aut_eq_finrank _ M).trans h2)⟩
  ·
    haveI : IsAlgClosed (InfinitePlace.Completion v) :=
      IsAlgClosed.of_ringEquiv _ _
        (InfinitePlace.Completion.ringEquivComplexOfIsComplex hv).symm
    have h1 := finrank_eq_one_of_isAlgClosed (InfinitePlace.Completion v) M
    refine ⟨K, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      v, rfl, ?_, ?_⟩
    · exact ⟨inferInstance, ⟨algEquivOfFinrankOne _ _ h1⟩⟩
    · exact ⟨galoisGroupMulEquivTrivial K _ _ h1⟩
section NormTraceCompletion
variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

/--
[algEquiv_eq_refl_of_finrank_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalGlobal.lean)
-/
@[path]
private lemma algEquiv_eq_refl_of_finrank_one_eq
  [Field F]
  [Field E]
  [Algebra F E]
  [FiniteDimensional F E]
  {e : E ≃ₐ[F] E}
-- given
  (h : Module.finrank F E = 1) :
-- imply
  e = AlgEquiv.refl := by
-- proof
  apply algEquiv_eq_refl_of_finrank_one h e

/--
[norm_baseChange_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalGlobal.lean)
-/
@[path]
private lemma norm_baseChange_eq_eq
  [Field K]
  [Field L]
  [NumberField K]
  [NumberField L]
  [Algebra K L]
  {v : HeightOneSpectrum (𝓞 K)}
  {α : L} :
-- imply
  algebraMap K (v.adicCompletion K) (Algebra.norm K α) = @Algebra.norm (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) _ _ Algebra.TensorProduct.rightAlgebra (α ⊗ₜ[K] (1 : v.adicCompletion K)) := by
-- proof
  apply norm_baseChange_eq v α

/--
[trace_baseChange_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalGlobal.lean)
-/
@[path]
private lemma trace_baseChange_eq_eq
  [Field K]
  [Field L]
  [NumberField K]
  [NumberField L]
  [Algebra K L]
  {v : HeightOneSpectrum (𝓞 K)}
  {α : L} :
-- imply
  algebraMap K (v.adicCompletion K) (Algebra.trace K L α) = @Algebra.trace (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) _ _ Algebra.TensorProduct.rightAlgebra (α ⊗ₜ[K] (1 : v.adicCompletion K)) := by
-- proof
  apply trace_baseChange_eq v α

/--
[norm_pi_fin'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalGlobal.lean)
-/
@[path]
private lemma norm_pi_fin'_eq
  [Field K]
  [Field L]
  [NumberField K]
  [NumberField L]
  [Algebra K L]
  [CommRing R]
  {n : ℕ}
  {A : Fin n → Type*}
  [∀ i, CommRing (A i)]
  [∀ i, Algebra R (A i)]
  [∀ i, Module.Free R (A i)]
  [∀ i, Module.Finite R (A i)]
-- given
  (f : ∀ i, A i) :
-- imply
  Algebra.norm R f = ∏ i, Algebra.norm R (f i) := by
-- proof
  apply norm_pi_fin' f

/--
[Algebra.norm_pi_apply'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalGlobal.lean)
-/
@[path]
private lemma norm_pi_apply'_eq
  [Field K]
  [Field L]
  [NumberField K]
  [NumberField L]
  [Algebra K L]
  [CommRing R]
  [Fintype ι]
  [DecidableEq ι]
  {A : ι → Type*}
  [∀ i, CommRing (A i)]
  [∀ i, Algebra R (A i)]
  [∀ i, Module.Free R (A i)]
  [∀ i, Module.Finite R (A i)]
-- given
  (f : ∀ i, A i) :
-- imply
  (Algebra.norm R) f = ∏ i, (Algebra.norm R) (f i) := by
-- proof
  apply Algebra.norm_pi_apply' f

/--
[algEquiv_tmul_one_component](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalGlobal.lean)
-/
@[path]
private lemma algEquiv_tmul_one_component_eq
  [Field K]
  [Field L]
  [NumberField K]
  [NumberField L]
  [Algebra K L]
  {v : HeightOneSpectrum (𝓞 K)}
  [Fintype { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }]
  {e : @AlgEquiv (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) ((w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }) → w.val.adicCompletion L) _ _ _ Algebra.TensorProduct.rightAlgebra (Pi.algebra _ _)}
  {α : L}
  {w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }}
-- given
  (localAlg : ∀ (w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }), Algebra (v.adicCompletion K) (w.val.adicCompletion L))
  (he : ∀ (α : L) (w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }), e (α ⊗ₜ[K] (1 : v.adicCompletion K)) w = algebraMap L (w.val.adicCompletion L) α) :
-- imply
  e (α ⊗ₜ[K] (1 : v.adicCompletion K)) w = algebraMap L (w.val.adicCompletion L) α := by
-- proof
  apply algEquiv_tmul_one_component v localAlg e he α w

/--
[norm_pi_eq_prod](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalGlobal.lean)
-/
@[path]
private lemma norm_pi_eq_prod_eq
  [Field K]
  [Field L]
  [NumberField K]
  [NumberField L]
  [Algebra K L]
  {v : HeightOneSpectrum (𝓞 K)}
  [Fintype { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }]
  {e : @AlgEquiv (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) ((w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }) → w.val.adicCompletion L) _ _ _ Algebra.TensorProduct.rightAlgebra (Pi.algebra _ _)}
  {α : L}
-- given
  (localAlg : ∀ (w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }), Algebra (v.adicCompletion K) (w.val.adicCompletion L))
  (he : ∀ (α : L) (w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }), e (α ⊗ₜ[K] (1 : v.adicCompletion K)) w = algebraMap L (w.val.adicCompletion L) α) :
-- imply
  @Algebra.norm (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) _ _ Algebra.TensorProduct.rightAlgebra (α ⊗ₜ[K] (1 : v.adicCompletion K)) = ∏ w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }, @Algebra.norm (v.adicCompletion K) (w.val.adicCompletion L) _ _ (localAlg w) (algebraMap L (w.val.adicCompletion L) α) := by
-- proof
  apply norm_pi_eq_prod v localAlg e he α

/--
[trace_single_comp_aux](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalGlobal.lean)
-/
@[path]
private lemma trace_single_comp_aux_eq
  [Field K]
  [Field L]
  [NumberField K]
  [NumberField L]
  [Algebra K L]
  [CommRing R]
  [Fintype ι]
  [DecidableEq ι]
  {A : ι → Type*}
  [∀ i, CommRing (A i)]
  [∀ i, Algebra R (A i)]
  [∀ i, Module.Free R (A i)]
  [∀ i, Module.Finite R (A i)]
  {j : ι}
  {f : A j →ₗ[R] A j} :
-- imply
  (LinearMap.trace R (∀ i, A i)) ((LinearMap.single R A j) ∘ₗ (f ∘ₗ (LinearMap.proj j))) = (LinearMap.trace R (A j)) f := by
-- proof
  apply trace_single_comp_aux j f

/--
[pi_lmul_decomp_aux](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalGlobal.lean)
-/
@[path]
private lemma pi_lmul_decomp_aux_eq
  [Field K]
  [Field L]
  [NumberField K]
  [NumberField L]
  [Algebra K L]
  [CommRing R]
  [Fintype ι]
  [DecidableEq ι]
  {A : ι → Type*}
  [∀ i, CommRing (A i)]
  [∀ i, Algebra R (A i)]
-- given
  (f : ∀ i, A i) :
-- imply
  (Algebra.lmul R (∀ i, A i) f) = ∑ i : ι, (LinearMap.single R A i).comp ((Algebra.lmul R (A i) (f i)).comp (LinearMap.proj i)) := by
-- proof
  apply pi_lmul_decomp_aux f

/--
[Algebra.trace_pi_apply'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalGlobal.lean)
-/
@[path]
private lemma trace_pi_apply'_eq
  [Field K]
  [Field L]
  [NumberField K]
  [NumberField L]
  [Algebra K L]
  [CommRing R]
  [Fintype ι]
  [DecidableEq ι]
  {A : ι → Type*}
  [∀ i, CommRing (A i)]
  [∀ i, Algebra R (A i)]
  [∀ i, Module.Free R (A i)]
  [∀ i, Module.Finite R (A i)]
-- given
  (f : ∀ i, A i) :
-- imply
  (Algebra.trace R (∀ i, A i)) f = ∑ i, (Algebra.trace R (A i)) (f i) := by
-- proof
  apply Algebra.trace_pi_apply' f

/--
[trace_pi_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalGlobal.lean)
-/
@[path]
private lemma trace_pi_eq_sum_eq
  [Field K]
  [Field L]
  [NumberField K]
  [NumberField L]
  [Algebra K L]
  {v : HeightOneSpectrum (𝓞 K)}
  [Fintype { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }]
  {e : @AlgEquiv (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) ((w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }) → w.val.adicCompletion L) _ _ _ Algebra.TensorProduct.rightAlgebra (Pi.algebra _ _)}
  {α : L}
-- given
  (localAlg : ∀ (w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }), Algebra (v.adicCompletion K) (w.val.adicCompletion L))
  (he : ∀ (α : L) (w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }), e (α ⊗ₜ[K] (1 : v.adicCompletion K)) w = algebraMap L (w.val.adicCompletion L) α) :
-- imply
  @Algebra.trace (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) _ _ Algebra.TensorProduct.rightAlgebra (α ⊗ₜ[K] (1 : v.adicCompletion K)) = ∑ w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }, @Algebra.trace (v.adicCompletion K) (w.val.adicCompletion L) _ _ (localAlg w) (algebraMap L (w.val.adicCompletion L) α) := by
-- proof
  apply trace_pi_eq_sum v localAlg e he α

/--
[norm_eq_prod_localNorm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalGlobal.lean)
-/
@[path]
private lemma norm_eq_prod_localNorm_eq
  [Field K]
  [Field L]
  [NumberField K]
  [NumberField L]
  [Algebra K L]
  {v : HeightOneSpectrum (𝓞 K)}
  [Fintype { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }]
  {α : L} :
-- imply
  algebraMap K (v.adicCompletion K) (Algebra.norm K α) = ∏ w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }, @Algebra.norm (v.adicCompletion K) (w.val.adicCompletion L) _ _ ((completionEmbedding_finite v w.val w.prop).toAlgebra) (algebraMap L (w.val.adicCompletion L) α) := by
-- proof
  apply norm_eq_prod_localNorm v α

/--
[trace_eq_sum_localTrace](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalGlobal.lean)
-/
@[path]
private lemma trace_eq_sum_localTrace_eq
  [Field K]
  [Field L]
  [NumberField K]
  [NumberField L]
  [Algebra K L]
  {v : HeightOneSpectrum (𝓞 K)}
  [Fintype { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }]
  {α : L} :
-- imply
  algebraMap K (v.adicCompletion K) (Algebra.trace K L α) = ∑ w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }, @Algebra.trace (v.adicCompletion K) (w.val.adicCompletion L) _ _ ((completionEmbedding_finite v w.val w.prop).toAlgebra) (algebraMap L (w.val.adicCompletion L) α) := by
-- proof
  apply trace_eq_sum_localTrace v α

/--
[norm_trace_completion_decomposition](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalGlobal.lean)
-/
@[path]
private lemma norm_trace_completion_decomposition_eq
  [Field K]
  [Field L]
  [NumberField K]
  [NumberField L]
  [Algebra K L]
  {v : HeightOneSpectrum (𝓞 K)}
  [Fintype { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }]
  {α : L} :
-- imply
  (algebraMap K (v.adicCompletion K) (Algebra.norm K α) = ∏ w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }, @Algebra.norm (v.adicCompletion K) (w.val.adicCompletion L) _ _ ((completionEmbedding_finite v w.val w.prop).toAlgebra) (algebraMap L (w.val.adicCompletion L) α)) ∧ (algebraMap K (v.adicCompletion K) (Algebra.trace K L α) = ∑ w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }, @Algebra.trace (v.adicCompletion K) (w.val.adicCompletion L) _ _ ((completionEmbedding_finite v w.val w.prop).toAlgebra) (algebraMap L (w.val.adicCompletion L) α)) := by
-- proof
  apply norm_trace_completion_decomposition v α


-- created on 2026-10-23
