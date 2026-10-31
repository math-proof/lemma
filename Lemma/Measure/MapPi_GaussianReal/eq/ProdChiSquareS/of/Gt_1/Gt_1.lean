import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.BigOperators.Fin
import Lemma.Measure.SumSqGaussians.eq.ChiSquaredReal
import Lemma.Finset.Sum_SquareSub_DivSum.eq.Sub_DivSquareSum
import Lemma.Real.MulInvSqrt.eq.MulSqrt_Div.of.Gt_0
import Lemma.Measure.MapGaussianReal.eq.GaussianReal
open MeasureTheory ProbabilityTheory Real WithLp Matrix Finset Measure
open scoped NNReal ENNReal RealInnerProductSpace
set_option maxHeartbeats 800000


/-! ### Helmert ONB -/

private noncomputable def allOnesUnit (n : Nat) : EuclideanSpace Real (Fin n) :=
  toLp 2 (fun _ : Fin n => (n : Real).sqrt⁻¹)

private lemma norm_allOnesUnit {n : Nat} (hn : 0 < n) : ‖allOnesUnit n‖ = 1 := by
  have hnpos : (0 : Real) < n := Nat.cast_pos.mpr hn
  have hc : 0 < (n : Real).sqrt⁻¹ := inv_pos.mpr (sqrt_pos.mpr hnpos)
  rw [allOnesUnit, EuclideanSpace.norm_eq]
  simp only [Real.norm_eq_abs, abs_of_pos hc]
  have hsum : (∑ _ : Fin n, ((n : Real).sqrt⁻¹) ^ 2) = (n : Real) * ((n : Real).sqrt⁻¹) ^ 2 := by
    simp [sum_const, card_univ, nsmul_eq_mul]
  rw [hsum, inv_pow, sq_sqrt hnpos.le, mul_inv_cancel₀ hnpos.ne', sqrt_one]

private lemma inner_allOnesUnit {n : Nat} (hn : 0 < n) (z : Fin n → Real) :
  ⟪allOnesUnit n, toLp 2 z⟫ = (n : Real).sqrt * ((∑ j, z j) / n) := by
  rw [allOnesUnit, EuclideanSpace.inner_toLp_toLp]
  change ∑ j : Fin n, z j * (n : Real).sqrt⁻¹ = _
  have hpull : ∑ j : Fin n, z j * (n : Real).sqrt⁻¹ = (n : Real).sqrt⁻¹ * ∑ j, z j := by
    simp [mul_comm (z _), mul_sum]
  rw [hpull, MulInvSqrt.eq.MulSqrt_Div.of.Gt_0 hn]

private lemma orthonormal_allOnesUnit {n : Nat} (hn : 0 < n) :
  Orthonormal Real (({(⟨0, hn⟩ : Fin n)} : Set (Fin n)).domRestrict fun _ => allOnesUnit n) := by
  have hsub : Subsingleton ↑({(⟨0, hn⟩ : Fin n)} : Set (Fin n)) := by
    refine ⟨fun a b => Subtype.ext ?_⟩
    exact (Set.eq_of_mem_singleton a.property).trans
      (Set.eq_of_mem_singleton b.property).symm
  refine ⟨fun i => ?_, Subsingleton.pairwise⟩
  simpa [Set.domRestrict_apply] using norm_allOnesUnit hn

private noncomputable def helmertBasis {n : Nat} (hn : 0 < n) :
  OrthonormalBasis (Fin n) Real (EuclideanSpace Real (Fin n)) :=
  Classical.choose
    (Orthonormal.exists_orthonormalBasis_extension_of_card_eq
      (E := EuclideanSpace Real (Fin n))
      (card_ι := by simp [finrank_euclideanSpace])
      (v := fun _ : Fin n => allOnesUnit n)
      (s := ({(⟨0, hn⟩ : Fin n)} : Set (Fin n)))
      (orthonormal_allOnesUnit hn))

private lemma helmertBasis_zero
  {n : Nat}
  (hn : 0 < n) :
  helmertBasis hn ⟨0, hn⟩ = allOnesUnit n :=
  (Classical.choose_spec
    (Orthonormal.exists_orthonormalBasis_extension_of_card_eq
      (E := EuclideanSpace Real (Fin n))
      (card_ι := by simp [finrank_euclideanSpace])
      (v := fun _ : Fin n => allOnesUnit n)
      (s := ({(⟨0, hn⟩ : Fin n)} : Set (Fin n)))
      (orthonormal_allOnesUnit hn))) ⟨0, hn⟩ (by simp)

private lemma helmert_coord_zero
  {n : Nat}
  (hn : 0 < n)
  (z : Fin n → Real) :
  (helmertBasis hn).repr (toLp 2 z) ⟨0, hn⟩ = (n : Real).sqrt * ((∑ j, z j) / n) := by
  rw [OrthonormalBasis.repr_apply_apply, helmertBasis_zero hn, inner_allOnesUnit hn]

/-! ### Parseval: SSE equals sum of non-mean Helmert coordinates squared -/

private lemma sum_sq_eq_helmert_tail {n : Nat} (hn : 0 < n) (z : Fin n → Real) :
  ∑ j : Fin n, (z j - (∑ k, z k) / n) ^ 2 =
      ∑ i ∈ (univ.erase (⟨0, hn⟩ : Fin n)),
        ((helmertBasis hn).repr (toLp 2 z) i) ^ 2 := by
  have hparseval :
    ∑ i : Fin n, ((helmertBasis hn).repr (toLp 2 z) i) ^ 2 =
        ‖(toLp 2 z : EuclideanSpace Real (Fin n))‖ ^ 2 := by
    simpa [OrthonormalBasis.repr_apply_apply] using
      (helmertBasis hn).sum_sq_inner_right (toLp 2 z)
  have hnorm :
    ‖(toLp 2 z : EuclideanSpace Real (Fin n))‖ ^ 2 = ∑ j : Fin n, z j ^ 2 := by
    simpa [WithLp.ofLp_toLp] using EuclideanSpace.real_norm_sq_eq (toLp 2 z)
  have h0 := helmert_coord_zero hn z
  have hsplit :
    ∑ i : Fin n, ((helmertBasis hn).repr (toLp 2 z) i) ^ 2 =
        ((helmertBasis hn).repr (toLp 2 z) ⟨0, hn⟩) ^ 2 +
          ∑ i ∈ univ.erase (⟨0, hn⟩ : Fin n),
            ((helmertBasis hn).repr (toLp 2 z) i) ^ 2 := by
    rw [← sum_erase_add (s := univ) (a := (⟨0, hn⟩ : Fin n)) (h := mem_univ _)]
    ring
  have hmean_sq :
    ((helmertBasis hn).repr (toLp 2 z) ⟨0, hn⟩) ^ 2 =
        (∑ k, z k) ^ 2 / (n : Real) := by
    rw [h0, mul_pow, sq_sqrt (Nat.cast_nonneg n)]
    field_simp [(Nat.cast_pos.mpr hn).ne']
  calc
    _ = (∑ j : Fin n, z j ^ 2) - (∑ k, z k) ^ 2 / (n : Real) := by
      simpa [card_univ] using
        Sum_SquareSub_DivSum.eq.Sub_DivSquareSum.fun
          (s := (univ : Finset (Fin n))) (a := z)
    _ = ‖(toLp 2 z : EuclideanSpace Real (Fin n))‖ ^ 2 -
        ((helmertBasis hn).repr (toLp 2 z) ⟨0, hn⟩) ^ 2 := by
      rw [hnorm, hmean_sq]
    _ = ∑ i : Fin n, ((helmertBasis hn).repr (toLp 2 z) i) ^ 2 -
        ((helmertBasis hn).repr (toLp 2 z) ⟨0, hn⟩) ^ 2 := by
      rw [← hparseval]
    _ = ∑ i ∈ univ.erase (⟨0, hn⟩ : Fin n),
        ((helmertBasis hn).repr (toLp 2 z) i) ^ 2 := by
      rw [hsplit]; ring

/-- Helmertized coordinates of a standard-Gaussian row are again product N(0,1). -/
private lemma map_helmert_eq_pi {n : Nat} (hn : 0 < n) :
  ((Measure.pi fun _ : Fin n => gaussianReal 0 1).map
      (fun z => WithLp.ofLp ((helmertBasis hn).repr (toLp 2 z)))) =
    (Measure.pi fun _ : Fin n => gaussianReal 0 1) := by
  have hstd :
    (Measure.pi fun _ : Fin n => gaussianReal 0 1).map (toLp 2) =
        stdGaussian (EuclideanSpace Real (Fin n)) :=
    map_pi_eq_stdGaussian
  have hrot :
    (stdGaussian (EuclideanSpace Real (Fin n))).map (helmertBasis hn).repr =
        stdGaussian (EuclideanSpace Real (Fin n)) :=
    stdGaussian_map (helmertBasis hn).repr
  have hmeas_toLp :
    Measurable (toLp 2 : (Fin n → Real) → EuclideanSpace Real (Fin n)) := by fun_prop
  have hmeas_repr : Measurable (helmertBasis hn).repr := by fun_prop
  have hmeas_ofLp :
    Measurable (WithLp.ofLp : EuclideanSpace Real (Fin n) → Fin n → Real) := by fun_prop
  have hmeas_ofLp_repr :
    Measurable (fun x : EuclideanSpace Real (Fin n) =>
      WithLp.ofLp ((helmertBasis hn).repr x)) :=
    hmeas_ofLp.comp hmeas_repr
  calc
    _ = ((Measure.pi fun _ : Fin n => gaussianReal 0 1).map (toLp 2)).map
      (fun x => WithLp.ofLp ((helmertBasis hn).repr x)) := by
      rw [Measure.map_map hmeas_ofLp_repr hmeas_toLp]; rfl
    _ = (stdGaussian (EuclideanSpace Real (Fin n))).map
      (fun x => WithLp.ofLp ((helmertBasis hn).repr x)) := by
      rw [hstd]
    _ = ((stdGaussian (EuclideanSpace Real (Fin n))).map (helmertBasis hn).repr).map
      WithLp.ofLp := by
      rw [Measure.map_map hmeas_ofLp hmeas_repr]; rfl
    _ = (stdGaussian (EuclideanSpace Real (Fin n))).map WithLp.ofLp := by
      rw [hrot]
    _ = ((Measure.pi fun _ : Fin n => gaussianReal 0 1).map (toLp 2)).map WithLp.ofLp := by
      rw [← hstd]
    _ = (Measure.pi fun _ : Fin n => gaussianReal 0 1).map (WithLp.ofLp ∘ toLp 2) := by
      rw [← Measure.map_map hmeas_ofLp hmeas_toLp]
    _ = (Measure.pi fun _ : Fin n => gaussianReal 0 1).map id := rfl
    _ = Measure.pi fun _ : Fin n => gaussianReal 0 1 := by
      simp [Measure.map_id]

/-! ### One-row: (√(k+1) · z̄, SSE) ~ N(0,1) × χ²(k) -/

private noncomputable def rowMean (k : Nat) (z : Fin (k + 1) → Real) : Real :=
  (∑ j, z j) / (k + 1 : Real)

private noncomputable def rowSSE (k : Nat) (z : Fin (k + 1) → Real) : Real :=
  ∑ j : Fin (k + 1), (z j - rowMean k z) ^ 2

private lemma helmert_coord_zero' (k : Nat) (z : Fin (k + 1) → Real) :
  (helmertBasis (Nat.succ_pos k)).repr (toLp 2 z) 0 =
      (k + 1 : Real).sqrt * rowMean k z := by
  simpa [rowMean, Fin.val_zero] using helmert_coord_zero (Nat.succ_pos k) z

private lemma sum_sq_eq_helmert_tail' (k : Nat) (z : Fin (k + 1) → Real) :
  rowSSE k z =
    ∑ j : Fin k, ((helmertBasis (Nat.succ_pos k)).repr (toLp 2 z)
      ((0 : Fin (k + 1)).succAbove j)) ^ 2 := by
  unfold rowSSE rowMean
  have htail := sum_sq_eq_helmert_tail (Nat.succ_pos k) z
  simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] at htail
  rw [htail]
  -- erase 0-sum = sum over Fin.succAbove 0
  change
    ∑ i ∈ univ.erase (0 : Fin (k + 1)),
      ((helmertBasis (Nat.succ_pos k)).repr (toLp 2 z) i) ^ 2 =
    ∑ j : Fin k, ((helmertBasis (Nat.succ_pos k)).repr (toLp 2 z)
      ((0 : Fin (k + 1)).succAbove j)) ^ 2
  set f : Fin (k + 1) → Real :=
    fun i => ((helmertBasis (Nat.succ_pos k)).repr (toLp 2 z) i) ^ 2
  change ∑ i ∈ univ.erase (0 : Fin (k + 1)), f i =
    ∑ j : Fin k, f ((0 : Fin (k + 1)).succAbove j)
  have hmem : ∀ x : Fin (k + 1), x ∈ univ.erase (0 : Fin (k + 1)) ↔ x ≠ 0 := by
    intro x; simp [mem_erase]
  rw [sum_subtype (s := univ.erase (0 : Fin (k + 1))) (p := fun x => x ≠ 0) hmem f]
  exact (Fintype.sum_equiv (finSuccAboveEquiv (0 : Fin (k + 1)))
    (fun j => f ((0 : Fin (k + 1)).succAbove j))
    (fun i => f i.val)
    (fun j => by simp [finSuccAboveEquiv])).symm

/-- Split product Gaussian on Fin (k+1) at index 0. -/
private lemma map_split_zero (k : Nat) :
  ((Measure.pi fun _ : Fin (k + 1) => gaussianReal 0 1).map
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => Real) 0)) =
    ((gaussianReal 0 1).prod (Measure.pi fun _ : Fin k => gaussianReal 0 1)) :=
  (measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => gaussianReal 0 1) 0).map_eq

/-- (first Helmert coord, sum of squares of the rest) pushforward. -/
private lemma map_coord_tail_sq (k : Nat) :
  ((Measure.pi fun _ : Fin (k + 1) => gaussianReal 0 1).map
      (fun c => (c 0, ∑ j : Fin k, (c ((0 : Fin (k + 1)).succAbove j)) ^ 2))) =
    ((gaussianReal 0 1).prod (Real.chiSquare k)) := by
  have hsplit := map_split_zero k
  have hmeas_split :
    Measurable (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => Real) 0) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => Real) 0).measurable
  have hmeas_tail :
    Measurable (fun p : Real × (Fin k → Real) => (p.1, ∑ j : Fin k, (p.2 j) ^ 2)) := by
    fun_prop
  have hcomp :
    (fun c : Fin (k + 1) → Real =>
          (c 0, ∑ j : Fin k, (c ((0 : Fin (k + 1)).succAbove j)) ^ 2)) =
        (fun p : Real × (Fin k → Real) => (p.1, ∑ j : Fin k, (p.2 j) ^ 2)) ∘
          (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => Real) 0) := by
    funext c
    -- piFinSuccAbove 0 = consEquiv.symm : c ↦ (c 0, Fin.tail c)
    -- and 0.succAbove j = j.succ = Fin.tail indexing
    change (c 0, ∑ j : Fin k, (c ((0 : Fin (k + 1)).succAbove j)) ^ 2) =
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => Real) 0 c).1,
        ∑ j : Fin k,
          ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => Real) 0 c).2 j) ^ 2)
    simp only [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv_zero,
      MeasurableEquiv.coe_mk]
    simp only [Fin.consEquiv_symm_apply, Fin.tail, Fin.succAbove_zero]
  calc
    _ = (Measure.pi fun _ : Fin (k + 1) => gaussianReal 0 1).map
      ((fun p : Real × (Fin k → Real) => (p.1, ∑ j : Fin k, (p.2 j) ^ 2)) ∘
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => Real) 0)) := by
      rw [hcomp]
    _ = ((Measure.pi fun _ : Fin (k + 1) => gaussianReal 0 1).map
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => Real) 0)).map
      (fun p => (p.1, ∑ j : Fin k, (p.2 j) ^ 2)) := by
      rw [Measure.map_map hmeas_tail hmeas_split]
    _ = ((gaussianReal 0 1).prod (Measure.pi fun _ : Fin k => gaussianReal 0 1)).map
      (fun p => (p.1, ∑ j : Fin k, (p.2 j) ^ 2)) := by
      rw [hsplit]
    _ = ((gaussianReal 0 1).map id).prod
      ((Measure.pi fun _ : Fin k => gaussianReal 0 1).map
        (fun t => ∑ j : Fin k, (t j) ^ 2)) := by
      rw [Measure.map_prod_map _ _ measurable_id (by fun_prop)]
      rfl
    _ = (gaussianReal 0 1).prod (sumSqGaussians k) := by
      simp only [Measure.map_id, sumSqGaussians]
    _ = (gaussianReal 0 1).prod (Real.chiSquare k) := by
      rw [SumSqGaussians.eq.ChiSquaredReal]

/-- One-row ANOVA coordinates under standard Gaussians. -/
private lemma map_mean_SSE_eq_prod (k : Nat) :
  ((Measure.pi fun _ : Fin (k + 1) => gaussianReal 0 1).map
    (fun z => ((k + 1 : Real).sqrt * rowMean k z, rowSSE k z))) =
    ((gaussianReal 0 1).prod (Real.chiSquare k)) := by
  have hhelmert := map_helmert_eq_pi (Nat.succ_pos k)
  have hcoord := map_coord_tail_sq k
  have hmeas_h :
    Measurable (fun z : Fin (k + 1) → Real =>
        WithLp.ofLp ((helmertBasis (Nat.succ_pos k)).repr (toLp 2 z))) := by
    fun_prop
  have hmeas_f :
    Measurable (fun c : Fin (k + 1) → Real =>
        (c 0, ∑ j : Fin k, (c ((0 : Fin (k + 1)).succAbove j)) ^ 2)) := by
    fun_prop
  have hfun :
    (fun z => ((k + 1 : Real).sqrt * rowMean k z, rowSSE k z)) =
        (fun c : Fin (k + 1) → Real =>
          (c 0, ∑ j : Fin k, (c ((0 : Fin (k + 1)).succAbove j)) ^ 2)) ∘
        (fun z => WithLp.ofLp ((helmertBasis (Nat.succ_pos k)).repr (toLp 2 z))) := by
    funext z
    refine Prod.ext ?_ ?_
    · simpa [Function.comp] using (helmert_coord_zero' k z).symm
    · simpa [Function.comp] using sum_sq_eq_helmert_tail' k z
  calc
    _ = (Measure.pi fun _ : Fin (k + 1) => gaussianReal 0 1).map
        ((fun c => (c 0, ∑ j : Fin k, (c ((0 : Fin (k + 1)).succAbove j)) ^ 2)) ∘
          (fun z => WithLp.ofLp ((helmertBasis (Nat.succ_pos k)).repr (toLp 2 z)))) := by
      rw [hfun]
    _ = ((Measure.pi fun _ : Fin (k + 1) => gaussianReal 0 1).map
        (fun z => WithLp.ofLp ((helmertBasis (Nat.succ_pos k)).repr (toLp 2 z)))).map
        (fun c => (c 0, ∑ j : Fin k, (c ((0 : Fin (k + 1)).succAbove j)) ^ 2)) := by
      rw [Measure.map_map hmeas_f hmeas_h]
    _ = (Measure.pi fun _ : Fin (k + 1) => gaussianReal 0 1).map
        (fun c => (c 0, ∑ j : Fin k, (c ((0 : Fin (k + 1)).succAbove j)) ^ 2)) := by
      rw [hhelmert]
    _ = (gaussianReal 0 1).prod (Real.chiSquare k) := hcoord

/-! ### Marginals of one-row: SSE ~ χ²(k), and deviations of m Gaussians -/

private lemma measurable_rowMean (k : Nat) : Measurable (rowMean k) := by
  unfold rowMean; fun_prop

private lemma measurable_rowSSE (k : Nat) : Measurable (rowSSE k) := by
  unfold rowSSE rowMean; fun_prop

private lemma map_SSE_eq_chiSquared (k : Nat) :
  (Measure.pi fun _ : Fin (k + 1) => gaussianReal 0 1).map (rowSSE k) = Real.chiSquare k := by
  have h := map_mean_SSE_eq_prod k
  have hmeas : Measurable (fun z : Fin (k + 1) → Real =>
    ((k + 1 : Real).sqrt * rowMean k z, rowSSE k z)) :=
    ((measurable_const.mul (measurable_rowMean k)).prodMk (measurable_rowSSE k))
  have hcomp :
    (Measure.pi fun _ : Fin (k + 1) => gaussianReal 0 1).map (rowSSE k) =
        ((Measure.pi fun _ : Fin (k + 1) => gaussianReal 0 1).map
          (fun z => ((k + 1 : Real).sqrt * rowMean k z, rowSSE k z))).map Prod.snd := by
    rw [Measure.map_map measurable_snd hmeas]; rfl
  have : IsProbabilityMeasure (gaussianReal 0 1) := inferInstance
  calc
    _ = ((gaussianReal 0 1).prod (Real.chiSquare k)).map Prod.snd := by
      rw [hcomp, h]
    _ = Real.chiSquare k := Measure.snd_prod

/-- ∑(xᵢ - x̄)² of m i.i.d. N(0,1) is χ²(m-1), for m = ℓ+1. -/
private lemma map_sum_sq_sub_mean_eq_chiSquared (ℓ : Nat) :
  ((Measure.pi fun _ : Fin (ℓ + 1) => gaussianReal 0 1).map
      (fun x => ∑ i : Fin (ℓ + 1), (x i - rowMean ℓ x) ^ 2)) =
    Real.chiSquare ℓ := by
  convert map_SSE_eq_chiSquared ℓ using 2
  funext x; rfl

/-! ### Curry: flat grid pi ↔ nested row pi -/

private lemma mem_uncurry_preimage_pi
  {ι κ : Type*}
  {t : (ι × κ) → Set Real}
  (rows : ι → κ → Real) :
  rows ∈ (MeasurableEquiv.curry ι κ Real).symm ⁻¹' (Set.univ.pi t) ↔ ∀ i j, rows i j ∈ t (i, j) := by
  simp [Set.mem_preimage, MeasurableEquiv.coe_curry_symm, Function.uncurry]

private lemma pi_map_uncurry
  {ι κ : Type*}
  [Fintype ι] [Fintype κ]
  (μ : Measure Real)
  [IsProbabilityMeasure μ] :
  ((Measure.pi fun _ : ι => Measure.pi fun _ : κ => μ).map
      (MeasurableEquiv.curry ι κ Real).symm) =
    (Measure.pi fun _ : ι × κ => μ) := by
  refine (Measure.pi_eq fun t ht => ?_).symm
  have hmeas : Measurable (MeasurableEquiv.curry ι κ Real).symm :=
    (MeasurableEquiv.curry ι κ Real).symm.measurable
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi ht)]
  have hpre :
    (MeasurableEquiv.curry ι κ Real).symm ⁻¹' (Set.univ.pi t) =
        Set.univ.pi (fun i : ι => Set.univ.pi (fun j : κ => t (i, j))) := by
    ext rows
    rw [mem_uncurry_preimage_pi]
    simp
  rw [hpre, Measure.pi_pi]
  simp_rw [Measure.pi_pi (fun _ : κ => μ)]
  exact (Fintype.prod_prod_type (fun p : ι × κ => μ (t p))).symm

private lemma pi_map_curry
  {ι κ : Type*}
  [Fintype ι] [Fintype κ]
  (μ : Measure Real)
  [IsProbabilityMeasure μ] :
  ((Measure.pi fun _ : ι × κ => μ).map (MeasurableEquiv.curry ι κ Real)) =
    (Measure.pi fun _ : ι => Measure.pi fun _ : κ => μ) := by
  have h := pi_map_uncurry (ι := ι) (κ := κ) μ
  set e := MeasurableEquiv.curry ι κ Real
  calc
    _ = ((Measure.pi fun _ : ι => Measure.pi fun _ : κ => μ).map e.symm).map e := by
      rw [← h]
    _ = Measure.pi fun _ : ι => Measure.pi fun _ : κ => μ :=
      MeasurableEquiv.map_map_symm e

private lemma sum_sq_curry_eq
  {ι κ : Type*}
  [Fintype ι] [Fintype κ]
  (y : (ι × κ) → Real) :
  ∑ p, (y p) ^ 2 = ∑ i : ι, ∑ j : κ, (y (i, j)) ^ 2 :=
  Fintype.sum_prod_type (fun p : ι × κ => (y p) ^ 2)

/-! ### Sum of i.i.d. χ²(k) = χ²(m*k) -/

private lemma map_sum_chiSquared (m k : Nat) :
  ((Measure.pi fun _ : Fin m => Real.chiSquare k).map (fun w => ∑ i, w i)) =
    Real.chiSquare (m * k) := by
  have hχ : ∀ n, Real.chiSquare n = sumSqGaussians n := fun n =>
    (SumSqGaussians.eq.ChiSquaredReal n).symm
  rw [hχ k, hχ (m * k)]
  unfold sumSqGaussians
  have : IsProbabilityMeasure (gaussianReal 0 1) := inferInstance
  have hcurry := pi_map_curry (ι := Fin m) (κ := Fin k) (gaussianReal 0 1)
  -- Reindex Fin (m*k) ≃ Fin m × Fin k
  have e : Fin (m * k) ≃ Fin m × Fin k := finProdFinEquiv.symm
  have hreindex :
    (Measure.pi fun _ : Fin (m * k) => gaussianReal 0 1).map
          (fun x => ∑ i, (x i) ^ 2) =
        (Measure.pi fun _ : Fin m × Fin k => gaussianReal 0 1).map
          (fun y => ∑ p, (y p) ^ 2) := by
    have hp := Measure.pi_map_piCongrLeft e (μ := fun _ => gaussianReal 0 1)
    set pe := MeasurableEquiv.piCongrLeft (fun _ : Fin m × Fin k => Real) e with hpe
    have hmeas_pe : Measurable pe := pe.measurable
    have hmeas_sq : Measurable (fun y : Fin m × Fin k → Real => ∑ p, (y p) ^ 2) := by
      fun_prop
    have hfun :
      (fun x : Fin (m * k) → Real => ∑ i, (x i) ^ 2) =
        (fun y : Fin m × Fin k → Real => ∑ p, (y p) ^ 2) ∘ ⇑pe := by
      funext x
      have hx : pe x = fun p => x (e.symm p) := by
        ext p
        -- for constant codomain Real, eqRec along apply_symm_apply is rfl
        simp only [hpe, MeasurableEquiv.piCongrLeft, MeasurableEquiv.coe_mk,
          Equiv.piCongrLeft_apply, eqRec_eq_cast, cast_eq]
      simp only [Function.comp, hx]
      exact Fintype.sum_equiv e (fun i => (x i) ^ 2)
        (fun p => (x (e.symm p)) ^ 2) fun i => by simp
    calc
      _ = (Measure.pi fun _ : Fin (m * k) => gaussianReal 0 1).map
          ((fun y => ∑ p, (y p) ^ 2) ∘ ⇑pe) := by
        rw [hfun]
      _ = ((Measure.pi fun _ : Fin (m * k) => gaussianReal 0 1).map pe).map
          (fun y => ∑ p, (y p) ^ 2) := by
        rw [Measure.map_map hmeas_sq hmeas_pe]
      _ = (Measure.pi fun _ : Fin m × Fin k => gaussianReal 0 1).map
          (fun y => ∑ p, (y p) ^ 2) := by
        rw [hp]
  -- Nested = flat via curry
  have hmeas_rows :
    Measurable (fun rows : Fin m → Fin k → Real =>
        ∑ i : Fin m, ∑ j : Fin k, (rows i j) ^ 2) := by fun_prop
  have hmeas_g :
    Measurable (fun rows : Fin m → Fin k → Real =>
        fun i => ∑ j : Fin k, (rows i j) ^ 2) := by fun_prop
  have hmeas_curry : Measurable (MeasurableEquiv.curry (Fin m) (Fin k) Real) :=
    (MeasurableEquiv.curry (Fin m) (Fin k) Real).measurable
  have hf : ∀ i : Fin m,
    AEMeasurable (fun x : Fin k → Real => ∑ j, (x j) ^ 2)
        (Measure.pi fun _ => gaussianReal 0 1) := fun _ =>
    (by fun_prop : Measurable (fun x : Fin k → Real => ∑ j, (x j) ^ 2)).aemeasurable
  have hpi :=
    Measure.pi_map_pi
      (μ := fun _ : Fin m => Measure.pi fun _ : Fin k => gaussianReal 0 1)
      (f := fun _ : Fin m => fun x : Fin k → Real => ∑ j, (x j) ^ 2) hf
  calc
    _ = ((Measure.pi fun _ : Fin m =>
          Measure.pi fun _ : Fin k => gaussianReal 0 1).map
        (fun rows i => ∑ j, (rows i j) ^ 2)).map (fun w => ∑ i, w i) := by
      rw [← hpi]
    _ = (Measure.pi fun _ : Fin m =>
        Measure.pi fun _ : Fin k => gaussianReal 0 1).map
        (fun rows => ∑ i, ∑ j, (rows i j) ^ 2) := by
      rw [Measure.map_map (by fun_prop) hmeas_g]; rfl
    _ = ((Measure.pi fun _ : Fin m × Fin k => gaussianReal 0 1).map
        (MeasurableEquiv.curry (Fin m) (Fin k) Real)).map
        (fun rows => ∑ i, ∑ j, (rows i j) ^ 2) := by
      rw [← hcurry]
    _ = (Measure.pi fun _ : Fin m × Fin k => gaussianReal 0 1).map
        ((fun rows => ∑ i, ∑ j, (rows i j) ^ 2) ∘
          MeasurableEquiv.curry (Fin m) (Fin k) Real) := by
      rw [← Measure.map_map hmeas_rows hmeas_curry]
    _ = (Measure.pi fun _ : Fin m × Fin k => gaussianReal 0 1).map
        (fun y => ∑ p, (y p) ^ 2) := by
      congr 1; funext y
      exact (sum_sq_curry_eq y).symm
    _ = (Measure.pi fun _ : Fin (m * k) => gaussianReal 0 1).map
        (fun x => ∑ i, (x i) ^ 2) := hreindex.symm

/-! ### Standard-case ANOVA joint law (μ=0, σ=1) -/

private noncomputable def anovaSB_std {ℓ k : Nat} (y : (Fin (ℓ + 1) × Fin (k + 1)) → Real) : Real :=
  (k + 1 : Real) * ∑ i, ((∑ j, y (i, j)) / (k + 1 : Real) - (∑ p, y p) / ((ℓ + 1) * (k + 1) : Real)) ^ 2

private noncomputable def anovaSW_std {ℓ k : Nat} (y : (Fin (ℓ + 1) × Fin (k + 1)) → Real) : Real :=
  ∑ i, ∑ j, (y (i, j) - (∑ t, y (i, t)) / (k + 1 : Real)) ^ 2

/-- Algebra: SB equals sum of squared deviations of scaled row means. -/
private lemma anovaSB_eq_sum_sq_U
  {ℓ k : Nat}
  (y : (Fin (ℓ + 1) × Fin (k + 1)) → Real) :
  anovaSB_std (ℓ := ℓ) (k := k) y =
    ∑ i, ((fun i' => (k + 1 : Real).sqrt * rowMean k (fun j => y (i', j))) i -
      rowMean ℓ (fun i' => (k + 1 : Real).sqrt * rowMean k (fun j => y (i', j)))) ^ 2 := by
  have hn0 : (k + 1 : Real) ≠ 0 := Nat.cast_add_one_ne_zero k
  have hm0 : (ℓ + 1 : Real) ≠ 0 := Nat.cast_add_one_ne_zero ℓ
  have hnpos : (0 : Real) < k + 1 := Nat.cast_add_one_pos k
  set U : Fin (ℓ + 1) → Real :=
    fun i => (k + 1 : Real).sqrt * rowMean k (fun j => y (i, j))
  set μbar : Real :=
    (∑ p : Fin (ℓ + 1) × Fin (k + 1), y p) / ((ℓ + 1 : Real) * (k + 1 : Real))
  have hflat : ∑ p : Fin (ℓ + 1) × Fin (k + 1), y p =
    ∑ i : Fin (ℓ + 1), ∑ j : Fin (k + 1), y (i, j) :=
    Fintype.sum_prod_type (fun p => y p)
  have hUbar : rowMean ℓ U = (k + 1 : Real).sqrt * μbar := by
    simp only [rowMean, U, μbar]
    have h1 :
      ∑ i, (k + 1 : Real).sqrt * ((∑ j, y (i, j)) / (k + 1 : Real)) =
        (k + 1 : Real).sqrt *
          ∑ i, (∑ j, y (i, j)) / (k + 1 : Real) := by
      simp [mul_sum]
    have h2 :
      ∑ i : Fin (ℓ + 1), (∑ j : Fin (k + 1), y (i, j)) / (k + 1 : Real) =
        (∑ i : Fin (ℓ + 1), ∑ j : Fin (k + 1), y (i, j)) / (k + 1 : Real) := by
      simp_rw [div_eq_mul_inv, ← Finset.sum_mul]
    rw [h1, h2, hflat, mul_div_assoc]
    field_simp [hm0, hn0]
  -- unfold SB
  unfold anovaSB_std
  -- goal: (k+1) * ∑ (ȳ_i - μbar)^2 = ∑ (U_i - Ū)^2
  rw [hUbar]
  have hterm : ∀ i,
    (k + 1 : Real) * (rowMean k (fun j => y (i, j)) - μbar) ^ 2 =
      ((k + 1 : Real).sqrt * rowMean k (fun j => y (i, j)) -
        (k + 1 : Real).sqrt * μbar) ^ 2 := by
    intro i
    have hsq : ((k + 1 : Real).sqrt) ^ 2 = (k + 1 : Real) := sq_sqrt hnpos.le
    calc
      _ = ((k + 1 : Real).sqrt) ^ 2 *
        (rowMean k (fun j => y (i, j)) - μbar) ^ 2 := by
        rw [hsq]
      _ = ((k + 1 : Real).sqrt * (rowMean k (fun j => y (i, j)) - μbar)) ^ 2 := by
        ring
      _ = ((k + 1 : Real).sqrt * rowMean k (fun j => y (i, j)) -
        (k + 1 : Real).sqrt * μbar) ^ 2 := by
        ring
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  -- left: (k+1)*(rowMean - μbar)^2 ; right: (U i - sqrt*μbar)^2
  simpa [U, rowMean] using hterm i

/-- Algebra: SW = ∑ᵢ rowSSE. -/
private lemma anovaSW_eq_sum_SSE
  {ℓ k : Nat}
  (y : (Fin (ℓ + 1) × Fin (k + 1)) → Real) :
  anovaSW_std (ℓ := ℓ) (k := k) y = ∑ i : Fin (ℓ + 1), rowSSE k (fun j => y (i, j)) := by
  unfold anovaSW_std rowSSE rowMean
  push_cast
  rfl

/-- Per-row (√n mean, SSE) of nested Gaussians → product of N(0,1)×χ²(k). -/
private lemma map_rows_mean_SSE (ℓ k : Nat) :
  ((Measure.pi fun _ : Fin (ℓ + 1) => Measure.pi fun _ : Fin (k + 1) => gaussianReal 0 1).map
    (fun rows : Fin (ℓ + 1) → Fin (k + 1) → Real =>
      fun i => ((k + 1 : Real).sqrt * rowMean k (rows i), rowSSE k (rows i)))) =
    (Measure.pi fun _ : Fin (ℓ + 1) => (gaussianReal 0 1).prod (Real.chiSquare k)) := by
  have hf : ∀ i : Fin (ℓ + 1),
    AEMeasurable
      (fun z : Fin (k + 1) → Real =>
        ((k + 1 : Real).sqrt * rowMean k z, rowSSE k z))
      (Measure.pi fun _ => gaussianReal 0 1) := fun _ =>
    (((measurable_const.mul (measurable_rowMean k)).prodMk
      (measurable_rowSSE k))).aemeasurable
  have hpi :=
    Measure.pi_map_pi
      (μ := fun _ : Fin (ℓ + 1) => Measure.pi fun _ : Fin (k + 1) => gaussianReal 0 1)
      (f := fun _ : Fin (ℓ + 1) => fun z : Fin (k + 1) → Real =>
        ((k + 1 : Real).sqrt * rowMean k z, rowSSE k z)) hf
  rw [hpi]
  congr 1; funext i
  exact map_mean_SSE_eq_prod k

/-- Split (mean,SSE) pairs into U-vector × W-vector. -/
private lemma map_arrow_prod_mean_SSE (ℓ k : Nat) :
  ((Measure.pi fun _ : Fin (ℓ + 1) => (gaussianReal 0 1).prod (Real.chiSquare k)).map
    (MeasurableEquiv.arrowProdEquivProdArrow Real Real (Fin (ℓ + 1)))) =
    ((Measure.pi fun _ : Fin (ℓ + 1) => gaussianReal 0 1).prod
      (Measure.pi fun _ : Fin (ℓ + 1) => Real.chiSquare k)) :=
  (measurePreserving_arrowProdEquivProdArrow Real Real (Fin (ℓ + 1))
    (fun _ => gaussianReal 0 1) (fun _ => Real.chiSquare k)).map_eq

/-- Main standard-case identity. -/
private lemma anova_std_eq_prod_chiSquared (ℓ k : Nat) :
  ((Measure.pi fun _ : Fin (ℓ + 1) × Fin (k + 1) => gaussianReal 0 1).map
      (fun y => (anovaSB_std (ℓ := ℓ) (k := k) y, anovaSW_std (ℓ := ℓ) (k := k) y))) =
    ((Real.chiSquare ℓ).prod (Real.chiSquare ((ℓ + 1) * k))) := by
  have : IsProbabilityMeasure (gaussianReal 0 1) := inferInstance
  have hcurry := pi_map_curry (ι := Fin (ℓ + 1)) (κ := Fin (k + 1)) (gaussianReal 0 1)
  have hrows := map_rows_mean_SSE ℓ k
  have harrow := map_arrow_prod_mean_SSE ℓ k
  set e_curry := MeasurableEquiv.curry (Fin (ℓ + 1)) (Fin (k + 1)) Real
  set e_arrow := MeasurableEquiv.arrowProdEquivProdArrow Real Real (Fin (ℓ + 1))
  have hmeas_curry : Measurable e_curry := e_curry.measurable
  have hmeas_arrow : Measurable e_arrow := e_arrow.measurable
  have hmeas_rows :
    Measurable (fun rows : Fin (ℓ + 1) → Fin (k + 1) → Real =>
        fun i => ((k + 1 : Real).sqrt * rowMean k (rows i), rowSSE k (rows i))) := by
    apply Measurable.of_eval
    intro i
    exact (measurable_const.mul ((measurable_rowMean k).comp (measurable_pi_apply i))).prodMk
      ((measurable_rowSSE k).comp (measurable_pi_apply i))
  -- g_pairs : nested rows → i ↦ (√n mean, SSE)
  set g_pairs :
    (Fin (ℓ + 1) → Fin (k + 1) → Real) → (Fin (ℓ + 1) → Real × Real) :=
    fun rows i => ((k + 1 : Real).sqrt * rowMean k (rows i), rowSSE k (rows i))
  set gUW : (Fin (ℓ + 1) × Fin (k + 1) → Real) →
    (Fin (ℓ + 1) → Real) × (Fin (ℓ + 1) → Real) :=
    fun y => e_arrow (g_pairs (e_curry y))
  set fSBW : (Fin (ℓ + 1) → Real) × (Fin (ℓ + 1) → Real) → Real × Real :=
    fun UW => (∑ i, (UW.1 i - rowMean ℓ UW.1) ^ 2, ∑ i, UW.2 i)
  have hmeas_pairs : Measurable g_pairs := hmeas_rows
  have hmeas_f : Measurable fSBW := by
    refine
      (((?_ : Measurable (fun U : Fin (ℓ + 1) → Real =>
          ∑ i, (U i - rowMean ℓ U) ^ 2)).comp measurable_fst).prodMk
        ((?_ : Measurable (fun W : Fin (ℓ + 1) → Real => ∑ i, W i)).comp
          measurable_snd))
    ·
      unfold rowMean; fun_prop
    ·
      fun_prop
  have hmeas_g : Measurable gUW :=
    hmeas_arrow.comp (hmeas_pairs.comp hmeas_curry)
  -- flat → (U,W)
  have hjoint_UW :
    (Measure.pi fun _ : Fin (ℓ + 1) × Fin (k + 1) => gaussianReal 0 1).map gUW =
        (Measure.pi fun _ : Fin (ℓ + 1) => gaussianReal 0 1).prod
          (Measure.pi fun _ : Fin (ℓ + 1) => Real.chiSquare k) := by
    have hcomp : gUW = e_arrow ∘ g_pairs ∘ e_curry := rfl
    rw [hcomp]
    -- f ∘ g ∘ h = f ∘ (g ∘ h); peel from the outside
    rw [← Measure.map_map hmeas_arrow (hmeas_pairs.comp hmeas_curry)]
    rw [← Measure.map_map hmeas_pairs hmeas_curry]
    rw [hcurry, hrows, harrow]
  -- (SB, SW) = fSBW ∘ gUW
  have hSBW :
    (fun y => (anovaSB_std (ℓ := ℓ) (k := k) y,
      anovaSW_std (ℓ := ℓ) (k := k) y)) = fSBW ∘ gUW := by
    funext y
    have hSB := anovaSB_eq_sum_sq_U (ℓ := ℓ) (k := k) y
    have hSW := anovaSW_eq_sum_SSE (ℓ := ℓ) (k := k) y
    have hU : (gUW y).1 = fun i =>
      (k + 1 : Real).sqrt * rowMean k (fun j => y (i, j)) := by
      -- e_curry y i = fun j => y (i,j); arrow splits
      rfl
    have hW : (gUW y).2 = fun i => rowSSE k (fun j => y (i, j)) := by
      rfl
    apply Prod.ext
    ·
      dsimp [fSBW, Function.comp]
      rwa [hU]
    ·
      dsimp [fSBW, Function.comp]
      rwa [hW]
  calc
    _ = (Measure.pi fun _ : Fin (ℓ + 1) × Fin (k + 1) => gaussianReal 0 1).map
      (fSBW ∘ gUW) := by
      rw [hSBW]
    _ = ((Measure.pi fun _ : Fin (ℓ + 1) × Fin (k + 1) => gaussianReal 0 1).map
      gUW).map fSBW := by
      rw [← Measure.map_map hmeas_f hmeas_g]
    _ = ((Measure.pi fun _ : Fin (ℓ + 1) => gaussianReal 0 1).prod
      (Measure.pi fun _ : Fin (ℓ + 1) => Real.chiSquare k)).map fSBW := by
      rw [hjoint_UW]
    _ = ((Measure.pi fun _ : Fin (ℓ + 1) => gaussianReal 0 1).map
      (fun U : Fin (ℓ + 1) → Real => ∑ i, (U i - rowMean ℓ U) ^ 2)).prod
      ((Measure.pi fun _ : Fin (ℓ + 1) => Real.chiSquare k).map
        (fun W : Fin (ℓ + 1) → Real => ∑ i, W i)) := by
      have hme1 : Measurable
        (fun U : Fin (ℓ + 1) → Real => ∑ i, (U i - rowMean ℓ U) ^ 2) := by
        unfold rowMean; fun_prop
      have hme2 : Measurable
        (fun W : Fin (ℓ + 1) → Real => ∑ i, W i) := by
        fun_prop
      have hProd :
        fSBW =
          Prod.map
            (fun U : Fin (ℓ + 1) → Real => ∑ i, (U i - rowMean ℓ U) ^ 2)
            (fun W : Fin (ℓ + 1) → Real => ∑ i, W i) := rfl
      rw [hProd]
      exact (Measure.map_prod_map
        (Measure.pi fun _ : Fin (ℓ + 1) => gaussianReal 0 1)
        (Measure.pi fun _ : Fin (ℓ + 1) => Real.chiSquare k)
        hme1 hme2).symm
    _ = (Real.chiSquare ℓ).prod (Real.chiSquare ((ℓ + 1) * k)) := by
      rw [map_sum_sq_sub_mean_eq_chiSquared ℓ, map_sum_chiSquared (ℓ + 1) k]


/-! ### Standardization and leaf main -/

/-- Product of i.i.d. Gaussians standardizes coordinatewise. -/
private lemma map_pi_std_gaussianReal
  {ι : Type*}
  [Fintype ι]
  {μ : ℝ}
  {σ : ℝ⁺} :
  ((Measure.pi fun _ : ι => gaussianReal μ (σ : NNReal)²).map
      (fun y : ι → ℝ => fun i => (y i - μ) / (σ : ℝ))) =
    (Measure.pi fun _ : ι => gaussianReal 0 1) := by
  have hcoord : ∀ i : ι,
    AEMeasurable (fun x : ℝ => (x - μ) / (σ : ℝ)) (gaussianReal μ (σ : NNReal)²) := fun _ =>
    ((measurable_id.sub measurable_const).div measurable_const).aemeasurable
  have hpi :=
    Measure.pi_map_pi (μ := fun _ : ι => gaussianReal μ (σ : NNReal)²)
      (f := fun _ : ι => fun x : ℝ => (x - μ) / (σ : ℝ)) hcoord
  rw [hpi]
  congr 1
  funext i
  exact MapGaussianReal.eq.GaussianReal (μ := μ) (σ := σ)

/-- SB under standardization: SB(z) = SB(y)/σ². -/
private lemma anovaSB_div_var_eq
  {ℓ k : Nat}
  {μ : ℝ}
  {σ : ℝ⁺}
  (y : (Fin (ℓ + 1) × Fin (k + 1)) → ℝ) :
  anovaSB_std (ℓ := ℓ) (k := k) (fun p => (y p - μ) / (σ : ℝ)) =
    anovaSB_std (ℓ := ℓ) (k := k) y / (σ : ℝ) ^ 2 := by
  have hσ0 : (σ : ℝ) ≠ 0 := ne_of_gt σ.property
  have hn0 : (k + 1 : ℝ) ≠ 0 := Nat.cast_add_one_ne_zero k
  have hm0 : (ℓ + 1 : ℝ) ≠ 0 := Nat.cast_add_one_ne_zero ℓ
  have hdiff (a b : ℝ) :
    (a - μ) / (σ : ℝ) - (b - μ) / (σ : ℝ) = (a - b) / (σ : ℝ) := by
    field_simp [hσ0]; ring
  dsimp only [anovaSB_std]
  -- goal is now without lets (dsimp reduces them)
  have hrow (i : Fin (ℓ + 1)) :
    (∑ j : Fin (k + 1), (y (i, j) - μ) / (σ : ℝ)) / (k + 1 : ℝ) =
        ((∑ j : Fin (k + 1), y (i, j)) / (k + 1 : ℝ) - μ) / (σ : ℝ) := by
    have hsum : ∑ j, (y (i, j) - μ) = ∑ j, y (i, j) - (k + 1 : ℝ) * μ := by
      simp [sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul]
    have hpull : ∑ j, (y (i, j) - μ) / (σ : ℝ) = (∑ j, (y (i, j) - μ)) / (σ : ℝ) := by
      simp_rw [div_eq_mul_inv, ← sum_mul]
    rw [hpull, hsum]; field_simp [hσ0, hn0]
  have hgrand :
    (∑ p : Fin (ℓ + 1) × Fin (k + 1), (y p - μ) / (σ : ℝ)) /
          ((ℓ + 1 : ℝ) * (k + 1 : ℝ)) =
        ((∑ p, y p) / ((ℓ + 1 : ℝ) * (k + 1 : ℝ)) - μ) / (σ : ℝ) := by
    have hsum : ∑ p, (y p - μ) =
        ∑ p, y p - ((ℓ + 1 : ℝ) * (k + 1 : ℝ)) * μ := by
      simp [sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, Fintype.card_prod]
    have hpull : ∑ p, (y p - μ) / (σ : ℝ) = (∑ p, (y p - μ)) / (σ : ℝ) := by
      simp_rw [div_eq_mul_inv, ← sum_mul]
    rw [hpull, hsum]; field_simp [hσ0, hn0, hm0]
  simp_rw [hrow, hgrand, hdiff, div_pow, div_eq_mul_inv]
  -- c * ∑ (a * inv) → ∑ c*(a*inv) → ∑ (c*a)*inv → (∑ c*a)*inv → (c*∑a)*inv → c*((∑a)*inv)
  rw [Finset.mul_sum]
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul, ← Finset.mul_sum, mul_assoc]

/-- SW under standardization: SW(z) = SW(y)/σ². -/
private lemma anovaSW_div_var_eq
  {ℓ k : Nat}
  {μ : ℝ}
  {σ : ℝ⁺}
  (y : (Fin (ℓ + 1) × Fin (k + 1)) → ℝ) :
  anovaSW_std (ℓ := ℓ) (k := k) (fun p => (y p - μ) / (σ : ℝ)) =
    anovaSW_std (ℓ := ℓ) (k := k) y / (σ : ℝ) ^ 2 := by
  have hσ0 : (σ : ℝ) ≠ 0 := ne_of_gt σ.property
  have hn0 : (k + 1 : ℝ) ≠ 0 := Nat.cast_add_one_ne_zero k
  have hdiff (a b : ℝ) :
    (a - μ) / (σ : ℝ) - (b - μ) / (σ : ℝ) = (a - b) / (σ : ℝ) := by
    field_simp [hσ0]; ring
  dsimp only [anovaSW_std]
  have hrow (i : Fin (ℓ + 1)) :
    (∑ t : Fin (k + 1), (y (i, t) - μ) / (σ : ℝ)) / (k + 1 : ℝ) =
        ((∑ t : Fin (k + 1), y (i, t)) / (k + 1 : ℝ) - μ) / (σ : ℝ) := by
    have hsum : ∑ t, (y (i, t) - μ) = ∑ t, y (i, t) - (k + 1 : ℝ) * μ := by
      simp [sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul]
    have hpull : ∑ t, (y (i, t) - μ) / (σ : ℝ) = (∑ t, (y (i, t) - μ)) / (σ : ℝ) := by
      simp_rw [div_eq_mul_inv, ← sum_mul]
    rw [hpull, hsum]; field_simp [hσ0, hn0]
  simp_rw [hrow]
  have hterm (i : Fin (ℓ + 1)) (j : Fin (k + 1)) :
    (y (i, j) - μ) / (σ : ℝ) -
          ((∑ t : Fin (k + 1), y (i, t)) / (k + 1 : ℝ) - μ) / (σ : ℝ) =
        (y (i, j) - (∑ t : Fin (k + 1), y (i, t)) / (k + 1 : ℝ)) / (σ : ℝ) := by
    exact hdiff _ _
  simp_rw [hterm, div_pow, div_eq_mul_inv]
  -- ∑∑ (a * inv) = (∑∑ a) * inv
  simp_rw [← Finset.sum_mul]

/-- General-(μ,σ) ANOVA identity on Fin (ℓ+1)×Fin (k+1). -/
private lemma anova_eq_prod_chiSquared
  (ℓ k : Nat)
  {μ : ℝ}
  {σ : ℝ⁺} :
  ((Measure.pi fun _ : Fin (ℓ + 1) × Fin (k + 1) => gaussianReal μ (σ : NNReal)²).map
      (fun y => (anovaSB_std (ℓ := ℓ) (k := k) y / (σ : ℝ) ^ 2,
        anovaSW_std (ℓ := ℓ) (k := k) y / (σ : ℝ) ^ 2))) =
    ((Real.chiSquare ℓ).prod (Real.chiSquare ((ℓ + 1) * k))) := by
  have hstd :=
    map_pi_std_gaussianReal (ι := Fin (ℓ + 1) × Fin (k + 1)) (μ := μ) (σ := σ)
  have hmeas_std : Measurable
    (fun y : Fin (ℓ + 1) × Fin (k + 1) → ℝ =>
        fun p => (y p - μ) / (σ : ℝ)) := by
    refine Measurable.of_eval fun p => ?_
    exact ((measurable_pi_apply p).sub measurable_const).div measurable_const
  have hmeas_SBW : Measurable
    (fun z : Fin (ℓ + 1) × Fin (k + 1) → ℝ =>
        (anovaSB_std (ℓ := ℓ) (k := k) z, anovaSW_std (ℓ := ℓ) (k := k) z)) := by
    unfold anovaSB_std anovaSW_std; fun_prop
  have hcomp :
    (fun y => (anovaSB_std (ℓ := ℓ) (k := k) y / (σ : ℝ) ^ 2,
          anovaSW_std (ℓ := ℓ) (k := k) y / (σ : ℝ) ^ 2)) =
        (fun z => (anovaSB_std (ℓ := ℓ) (k := k) z,
            anovaSW_std (ℓ := ℓ) (k := k) z)) ∘
          (fun y p => (y p - μ) / (σ : ℝ)) := by
    funext y
    apply Prod.ext
    · exact (anovaSB_div_var_eq (ℓ := ℓ) (k := k) (μ := μ) (σ := σ) y).symm
    · exact (anovaSW_div_var_eq (ℓ := ℓ) (k := k) (μ := μ) (σ := σ) y).symm
  rw [hcomp, ← Measure.map_map hmeas_SBW hmeas_std, hstd,
    anova_std_eq_prod_chiSquared ℓ k]

/--
One-way ANOVA between/within sums of squares under i.i.d. Gaussians (H₀).

Balanced grid `y : Fin m × Fin n → ℝ` with law
`Measure.pi (fun _ ↦ gaussianReal μ (σ : NNReal)²)`, assumptions `1 < m`,
`1 < n`, and `σ : ℝ⁺` (cast to `NNReal` at the margin).

Per sample:
* grand mean `μ̄ = (∑ p, y p) / (m * n)`
* row mean `ȳᵢ = (∑ j, y (i, j)) / n`
* `SB = n * ∑ᵢ (ȳᵢ - μ̄)²`
* `SW = ∑ᵢ ∑ⱼ (y (i, j) - ȳᵢ)²`

Claim: `(SB / σ², SW / σ²)` has law
`(Real.chiSquare (m - 1)).prod (Real.chiSquare (m * (n - 1)))`
(Helmert / Cochran via per-row orthonormal Helmert and product Gaussian structure).
-/
@[path]
private lemma main
  {m n : ℕ} {μ : ℝ} {σ : ℝ⁺}
-- given
  (hm : 1 < m)
  (hn : 1 < n) :
-- imply
  (Measure.pi fun _ : Fin m × Fin n ↦ gaussianReal μ (σ : NNReal)²).map
      (fun y ↦
        (((n : ℝ) *
            ∑ i : Fin m,
              ((∑ j : Fin n, y (i, j)) / (n : ℝ) -
                (∑ p : Fin m × Fin n, y p) / (m * n : ℝ)) ^ 2) /
          (σ : ℝ) ^ 2,
          (∑ i : Fin m, ∑ j : Fin n,
              (y (i, j) - (∑ k : Fin n, y (i, k)) / (n : ℝ)) ^ 2) /
            (σ : ℝ) ^ 2)) =
    (Real.chiSquare (m - 1)).prod (Real.chiSquare (m * (n - 1))) := by
-- proof
  obtain ⟨ℓ, rfl⟩ : ∃ ℓ, m = ℓ + 1 :=
    ⟨m - 1, (Nat.succ_pred_eq_of_pos (Nat.zero_lt_of_lt hm)).symm⟩
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 :=
    ⟨n - 1, (Nat.succ_pred_eq_of_pos (Nat.zero_lt_of_lt hn)).symm⟩
  have hdeg1 : (ℓ + 1) - 1 = ℓ := Nat.add_sub_cancel ℓ 1
  have hdeg2 : (ℓ + 1) * ((k + 1) - 1) = (ℓ + 1) * k := by
    rw [Nat.add_sub_cancel]
  simp only [hdeg1, hdeg2]
  convert anova_eq_prod_chiSquared ℓ k (μ := μ) (σ := σ) using 1
  ·
    refine congrArg (fun f => Measure.map f _) ?_
    funext y
    apply Prod.ext
    ·
      simp only [anovaSB_std]
      push_cast
      rfl
    ·
      simp only [anovaSW_std]
      push_cast
      rfl


-- created on 2026-10-30
-- updated on 2026-10-31
