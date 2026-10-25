import Lemma.NumberField.StandardGlobalAddChar

open Function IsDedekindDomain NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion

noncomputable section

namespace NumberField.StandardAddChar

section ArchPrelim

variable {K : Type*} [Field K]

theorem extensionEmbedding_algebraMap (v : InfinitePlace K) (x : K) :
    extensionEmbedding v (algebraMap K v.Completion x) = v.embedding x := by
  have h1 : algebraMap K v.Completion x = ((WithAbs.equiv v.1).symm x : v.Completion) := rfl
  rw [h1, extensionEmbedding_coe, RingEquiv.apply_symm_apply]

end ArchPrelim

section RatSide

theorem isReal_rat_infinitePlace (v : InfinitePlace ℚ) : IsReal v :=
  IsTotallyReal.isReal v

def ratArchLine : ℝ →+ InfiniteAdeleRing ℚ where
  toFun r := fun v => (ringEquivRealOfIsReal (isReal_rat_infinitePlace v)).symm r
  map_zero' := by
    funext v; exact map_zero _
  map_add' r s := by
    funext v; exact map_add _ r s

@[simp] theorem ratArchLine_apply (r : ℝ) (v : InfinitePlace ℚ) :
    ratArchLine r v = (ringEquivRealOfIsReal (isReal_rat_infinitePlace v)).symm r := rfl

theorem ratArchLine_ratCast (q : ℚ) :
    ratArchLine (q : ℝ) = algebraMap ℚ (InfiniteAdeleRing ℚ) q := by
  funext v
  show (ringEquivRealOfIsReal (isReal_rat_infinitePlace v)).symm (q : ℝ)
      = algebraMap ℚ v.Completion q
  rw [RingEquiv.symm_apply_eq, ringEquivRealOfIsReal_apply,
    eq_ratCast (algebraMap ℚ v.Completion) q]
  exact (map_ratCast (extensionEmbeddingOfIsReal (isReal_rat_infinitePlace v)) q).symm

theorem ratArchLine_surjective : Function.Surjective ratArchLine := by
  intro y
  refine ⟨ringEquivRealOfIsReal (isReal_rat_infinitePlace default) (y default), ?_⟩
  funext v
  obtain rfl : (default : InfinitePlace ℚ) = v := Subsingleton.elim _ _
  exact (ringEquivRealOfIsReal _).symm_apply_apply _

theorem continuous_ratArchLine : Continuous ratArchLine := by
  refine continuous_pi fun v => ?_
  show Continuous fun r => (ringEquivRealOfIsReal (isReal_rat_infinitePlace v)).symm r
  have : (fun r => (ringEquivRealOfIsReal (isReal_rat_infinitePlace v)).symm r)
      = (isometryEquivRealOfIsReal (isReal_rat_infinitePlace v)).symm := rfl
  rw [this]
  exact (isometryEquivRealOfIsReal (isReal_rat_infinitePlace v)).symm.continuous

end RatSide

section ArchTrace

variable (K : Type*) [Field K] [NumberField K]

def infTraceSum (x : InfiniteAdeleRing K) : ℝ :=
  ∑ w : InfinitePlace K, (mult w : ℝ) * (extensionEmbedding w (x w)).re

theorem infTraceSum_zero : infTraceSum K 0 = 0 := by
  unfold infTraceSum
  refine Finset.sum_eq_zero fun w _ => ?_
  show (mult w : ℝ) * (extensionEmbedding w (0 : w.Completion)).re = 0
  rw [map_zero, Complex.zero_re, mul_zero]

theorem infTraceSum_add (x y : InfiniteAdeleRing K) :
    infTraceSum K (x + y) = infTraceSum K x + infTraceSum K y := by
  unfold infTraceSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  show (mult w : ℝ) * (extensionEmbedding w (x w + y w)).re = _
  rw [map_add, Complex.add_re, mul_add]

def infTraceSumHom : InfiniteAdeleRing K →+ ℝ where
  toFun := infTraceSum K
  map_zero' := infTraceSum_zero K
  map_add' := infTraceSum_add K

set_option maxHeartbeats 1000000 in

theorem trace_eq_sum_mult_embedding_re (x : K) :
    ((Algebra.trace ℚ K x : ℚ) : ℝ)
      = ∑ w : InfinitePlace K, (mult w : ℝ) * (InfinitePlace.embedding w x).re := by
  classical
  apply Complex.ofReal_injective
  have hA : ((((Algebra.trace ℚ K x : ℚ) : ℝ)) : ℂ) = ∑ φ : K →+* ℂ, φ x := by
    have h1 : ((((Algebra.trace ℚ K x : ℚ) : ℝ)) : ℂ)
        = algebraMap ℚ ℂ (Algebra.trace ℚ K x) := by
      rw [eq_ratCast (algebraMap ℚ ℂ)]; push_cast; rfl
    rw [h1, trace_eq_sum_embeddings ℂ,
      ← Equiv.sum_comp (RingHom.equivRatAlgHom _ _) (fun σ : K →ₐ[ℚ] ℂ => σ x)]
    rfl
  rw [hA, ← Finset.sum_fiberwise Finset.univ (fun φ : K →+* ℂ => InfinitePlace.mk φ)
    (fun φ => φ x)]
  push_cast
  refine Finset.sum_congr rfl fun w _ => ?_
  have hfilter : Finset.filter (fun φ : K →+* ℂ => InfinitePlace.mk φ = w) Finset.univ
      = {InfinitePlace.embedding w, ComplexEmbedding.conjugate (InfinitePlace.embedding w)} := by
    ext φ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro h
      have h2 : InfinitePlace.mk φ = InfinitePlace.mk (InfinitePlace.embedding w) := by
        rw [InfinitePlace.mk_embedding]; exact h
      rcases InfinitePlace.mk_eq_iff.mp h2 with h3 | h3
      · exact Or.inl h3
      · exact Or.inr (h3 ▸ (star_star φ).symm)
    · rintro (rfl | rfl)
      · exact InfinitePlace.mk_embedding w
      · rw [InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]
  rw [hfilter]
  rcases InfinitePlace.isReal_or_isComplex w with hw | hw
  · rw [InfinitePlace.conjugate_embedding_eq_of_isReal hw, Finset.pair_eq_singleton,
      Finset.sum_singleton, mult_isReal ⟨_, hw⟩]
    have hre : (starRingEnd ℂ) (InfinitePlace.embedding w x) = InfinitePlace.embedding w x := by
      rw [← ComplexEmbedding.conjugate_coe_eq, InfinitePlace.conjugate_embedding_eq_of_isReal hw]
    conv_lhs => rw [← Complex.conj_eq_iff_re.mp hre]
    push_cast; ring
  · have hne : InfinitePlace.embedding w
        ≠ ComplexEmbedding.conjugate (InfinitePlace.embedding w) := by
      intro h
      exact (not_isReal_iff_isComplex.mpr hw)
        (InfinitePlace.isReal_iff.mpr (ComplexEmbedding.isReal_iff.mpr h.symm))
    rw [Finset.sum_pair hne, ComplexEmbedding.conjugate_coe_eq, Complex.add_conj,
      mult_isComplex ⟨_, hw⟩]
    push_cast; ring

theorem infTraceSum_algebraMap (x : K) :
    infTraceSum K (algebraMap K (InfiniteAdeleRing K) x) = ((Algebra.trace ℚ K x : ℚ) : ℝ) := by
  rw [trace_eq_sum_mult_embedding_re K x]
  unfold infTraceSum
  refine Finset.sum_congr rfl fun w _ => ?_
  congr 1
  rw [show algebraMap K (InfiniteAdeleRing K) x w = algebraMap K w.Completion x from rfl,
    extensionEmbedding_algebraMap]

theorem continuous_infTraceSum : Continuous (infTraceSum K) := by
  unfold infTraceSum
  refine continuous_finsetSum _ fun w _ => ?_
  exact continuous_const.mul
    (Complex.continuous_re.comp (((isometry_extensionEmbedding w).continuous).comp (continuous_apply w)))

theorem infTraceSum_surjective : Function.Surjective (infTraceSum K) := by
  classical
  intro r
  obtain ⟨w₀⟩ := (inferInstance : Nonempty (InfinitePlace K))
  rcases InfinitePlace.isReal_or_isComplex w₀ with hw | hw
  · obtain ⟨z, hz⟩ := surjective_extensionEmbeddingOfIsReal hw r
    refine ⟨Pi.single w₀ z, ?_⟩
    unfold infTraceSum
    rw [Finset.sum_eq_single w₀]
    · rw [Pi.single_eq_same, mult_isReal ⟨_, hw⟩, ← extensionEmbeddingOfIsReal_apply hw,
        hz]
      simp
    · intro w _ hwne
      rw [Pi.single_eq_of_ne hwne, map_zero, Complex.zero_re, mul_zero]
    · intro h; exact absurd (Finset.mem_univ w₀) h
  · obtain ⟨z, hz⟩ := surjective_extensionEmbedding_of_isComplex hw ((r / 2 : ℝ) : ℂ)
    refine ⟨Pi.single w₀ z, ?_⟩
    unfold infTraceSum
    rw [Finset.sum_eq_single w₀]
    · rw [Pi.single_eq_same, mult_isComplex ⟨_, hw⟩, hz, Complex.ofReal_re]
      push_cast; ring
    · intro w _ hwne
      rw [Pi.single_eq_of_ne hwne, map_zero, Complex.zero_re, mul_zero]
    · intro h; exact absurd (Finset.mem_univ w₀) h

end ArchTrace

section TraceInfHom

variable (K : Type*) [Field K] [NumberField K]

def traceInfHom : InfiniteAdeleRing K →+ InfiniteAdeleRing ℚ :=
  ratArchLine.comp (infTraceSumHom K)

theorem traceInfHom_apply (x : InfiniteAdeleRing K) :
    traceInfHom K x = ratArchLine (infTraceSum K x) := rfl

theorem traceInfHom_algebraMap (x : K) :
    traceInfHom K (algebraMap K (InfiniteAdeleRing K) x)
      = algebraMap ℚ (InfiniteAdeleRing ℚ) (Algebra.trace ℚ K x) := by
  rw [traceInfHom_apply, infTraceSum_algebraMap, ratArchLine_ratCast]

theorem continuous_traceInfHom : Continuous (traceInfHom K) :=
  continuous_ratArchLine.comp (continuous_infTraceSum K)

theorem traceInfHom_surjective : Function.Surjective (traceInfHom K) :=
  ratArchLine_surjective.comp (infTraceSum_surjective K)

end TraceInfHom

variable (F : Type) [Field F] [NumberField F]

def archTraceDataOf
    (traceFin : FiniteAdeleRing (𝓞 F) F →+ FiniteAdeleRing (𝓞 ℚ) ℚ)
    (traceFin_algebraMap : ∀ x : F, traceFin (algebraMap F _ x)
      = algebraMap ℚ _ (Algebra.trace ℚ F x))
    (continuous_traceFin : Continuous traceFin) :
    AdelicTraceData F where
  traceFin := traceFin
  traceInf := traceInfHom F
  traceFin_algebraMap := traceFin_algebraMap
  traceInf_algebraMap := traceInfHom_algebraMap F
  continuous_traceFin := continuous_traceFin
  continuous_traceInf := continuous_traceInfHom F
  traceInf_surjective := traceInfHom_surjective F

example : AdelicTraceData ℚ :=
  archTraceDataOf ℚ ratTraceData.traceFin ratTraceData.traceFin_algebraMap
    ratTraceData.continuous_traceFin

end NumberField.StandardAddChar

end
