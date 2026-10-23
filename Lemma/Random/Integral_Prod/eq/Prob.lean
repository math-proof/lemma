import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Count
import Lemma.Random.All_EqIntegral_ProbJoint.of.PSpace_Joint
import Lemma.Random.All_Eq_MulProbCond.of.PSpace_Joint
open MeasureTheory Random


private noncomputable def density
  [MeasurableSpace Ω]
  [ReferenceMeasure α]
  {π : Measure Ω}
  {s : ℕ → Ω → α}
  [SinglePSpace π (s 0)]
  {n : ℕ}
  (hT : ∀ t : ℕ, SinglePSpace π (s (t + 1), s t))
  (v : α) (u : Fin n → α) : ENNReal :=
  let path : Fin (n + 1) → α := Fin.snoc (α := fun _ => α) u v
  π.prob (s 0) (path 0) *
    ∏ t : Fin n,
      @MeasureTheory.Measure.condProb Ω α α _ _ _ π (s (t + 1), s t.val) (hT t.val)
        (path t.succ, path t.castSucc)


private lemma singlePSpace_s
  [MeasurableSpace Ω]
  [ReferenceMeasure α]
  {π : Measure Ω}
  {s : ℕ → Ω → α}
  [SinglePSpace π (s 0)]
  {n : ℕ}
  (hT : ∀ t : ℕ, SinglePSpace π (s (t + 1), s t)) :
  SinglePSpace π (s n) := by
  induction n with
  | zero => assumption
  | succ n _ => exact PSpace.of.PSpace_Joint.fst (hT n)


private lemma density_zero
  [MeasurableSpace Ω]
  [ReferenceMeasure α]
  {π : Measure Ω}
  {s : ℕ → Ω → α}
  [SinglePSpace π (s 0)]
  (hT : ∀ t : ℕ, SinglePSpace π (s (t + 1), s t))
  (v : α) :
  density (s := s) (n := 0) hT v Fin.elim0 = π.prob (s 0) v := by
  simp [density, Fin.snoc_zero]


private lemma integral_probJoint_fst
  [MeasurableSpace Ω]
  [ReferenceMeasure α] [ReferenceMeasure β]
  [Countable α] [MeasurableSingletonClass α]
  {π : Measure Ω}
  {x : Ω → α} {y : Ω → β}
  (hP : SinglePSpace π (x, y))
  (hα : ReferenceMeasure.measure (α := α) = Measure.count)
  (v : α) :
  have := PSpace.of.PSpace_Joint.fst hP
  ∫⁻ w : β, π.prob (x, y) (v, w) ∂ReferenceMeasure.measure =
    π.prob x v := by
  have hmain := All_EqIntegral_ProbJoint.of.PSpace_Joint hP
  simp at hmain
  rw [hα] at hmain
  exact Measure.ae_count_iff.mp hmain v


private lemma mulProbJoint_fst
  [MeasurableSpace Ω]
  [ReferenceMeasure α] [ReferenceMeasure β]
  [Countable α] [MeasurableSingletonClass α]
  {π : Measure Ω}
  {x : Ω → α} {y : Ω → β}
  (hP : SinglePSpace π (x, y))
  (hα : ReferenceMeasure.measure (α := α) = Measure.count)
  (v : α) :
  have := PSpace.of.PSpace_Joint.snd hP
  (fun w : β =>
      π.prob y w *
        @MeasureTheory.Measure.condProb Ω α β _ _ _ π (x, y) hP (v, w)) =ᵐ[ReferenceMeasure.measure]
    fun w : β => π.prob (x, y) (v, w) := by
  have hmul := All_Eq_MulProbCond.of.PSpace_Joint hP
  rw [hα, Measure.ae_count_iff] at hmul
  exact (hmul v).mono fun w h => (mul_comm _ _).trans h.symm


private lemma density_snoc
  [MeasurableSpace Ω]
  [ReferenceMeasure α]
  {π : Measure Ω}
  {s : ℕ → Ω → α}
  [SinglePSpace π (s 0)]
  {n : ℕ}
  (hT : ∀ t : ℕ, SinglePSpace π (s (t + 1), s t))
  (v w₀ : α) (w : Fin n → α) :
  density (s := s) (n := n + 1) hT v (Fin.snoc (α := fun _ => α) w w₀) =
    density (s := s) (n := n) hT w₀ w *
      @MeasureTheory.Measure.condProb Ω α α _ _ _ π (s (n + 1), s n) (hT n) (v, w₀) := by
  set path' : Fin (n + 1) → α := Fin.snoc (α := fun _ => α) w w₀
  set path : Fin (n + 2) → α := Fin.snoc (α := fun _ => α) path' v
  have hprod :
    ∏ t : Fin (n + 1),
      @MeasureTheory.Measure.condProb Ω α α _ _ _ π (s (t.val + 1), s t.val) (hT t.val)
        (path t.succ, path t.castSucc) =
    (∏ t : Fin n,
      @MeasureTheory.Measure.condProb Ω α α _ _ _ π (s (t.val + 1), s t.val) (hT t.val)
        (path' t.succ, path' t.castSucc)) *
      @MeasureTheory.Measure.condProb Ω α α _ _ _ π (s (n + 1), s n) (hT n) (v, w₀) := by
    rw [Fin.prod_univ_castSucc]
    congr 1
    ·
      apply Finset.prod_congr rfl
      intro i _
      simp only [path, path']
      rw [Fin.snoc_castSucc, Fin.snoc_castSucc, Fin.succ_castSucc, Fin.snoc_castSucc]
      rfl
    ·
      simp [path, path', Fin.snoc_last, Fin.succ_last]
  rw [density, density, hprod]
  simp only [path', Fin.snoc_castSucc]
  ac_rfl


private lemma measurable_density
  [MeasurableSpace Ω]
  [ReferenceMeasure α]
  {π : Measure Ω}
  {s : ℕ → Ω → α}
  [SinglePSpace π (s 0)]
  {n : ℕ}
  (hT : ∀ t : ℕ, SinglePSpace π (s (t + 1), s t))
  {v : α} :
  Measurable (density (s := s) (n := n) hT v) := by
  have hpath : Measurable (fun u : Fin n → α => Fin.snoc (α := fun _ => α) u v) := by
    refine measurable_pi_iff.2 fun i => ?_
    refine Fin.lastCases ?_ (fun j => ?_) i
    ·
      convert measurable_const (a := v) using 1
      funext u
      simp [Fin.snoc_last]
    ·
      convert measurable_pi_apply j using 1
      funext u
      simp [Fin.snoc_castSucc]
  apply Measurable.mul
  ·
    exact (Measure.measurable_rnDeriv (π.map (s 0)) _).comp
      ((measurable_pi_apply (0 : Fin (n + 1))).comp hpath)
  ·
    refine Finset.measurable_prod Finset.univ fun t _ => ?_
    unfold Measure.condProb
    apply Measurable.div
    ·
      exact (Measure.measurable_rnDeriv (π.map (s (t + 1), s t)) _).comp
        (Measurable.prodMk
          ((measurable_pi_apply (t.succ : Fin (n + 1))).comp hpath)
          ((measurable_pi_apply (t.castSucc : Fin (n + 1))).comp hpath))
    ·
      exact (Measure.measurable_rnDeriv (π.map (s t)) _).comp
        ((measurable_pi_apply (t.castSucc : Fin (n + 1))).comp hpath)


private lemma lintegral_density_snoc
  [MeasurableSpace Ω]
  [ReferenceMeasure α]
  {π : Measure Ω}
  {s : ℕ → Ω → α}
  [SinglePSpace π (s 0)]
  {n : ℕ}
  (hT : ∀ t : ℕ, SinglePSpace π (s (t + 1), s t))
  (v : α) :
  ∫⁻ u : Fin (n + 1) → α,
      density (s := s) (n := n + 1) hT v u
    ∂(Measure.pi fun _ => ReferenceMeasure.measure) =
    ∫⁻ w₀ : α, ∫⁻ w : Fin n → α,
        density (s := s) (n := n) hT w₀ w *
          @MeasureTheory.Measure.condProb Ω α α _ _ _ π (s (n + 1), s n) (hT n) (v, w₀)
      ∂(Measure.pi fun _ => ReferenceMeasure.measure)
      ∂ReferenceMeasure.measure := by
  let μ := ReferenceMeasure.measure (α := α)
  let e' := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) (Fin.last n)
  have hmp :
    MeasurePreserving e' (Measure.pi fun _ => μ) (μ.prod (Measure.pi fun _ : Fin n => μ)) :=
    measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) (Fin.last n)
  have hmp' :
    MeasurePreserving e'.symm (μ.prod (Measure.pi fun _ : Fin n => μ)) (Measure.pi fun _ => μ) :=
    hmp.symm
  have heq : ∀ (w₀ : α) (w : Fin n → α), e'.symm (w₀, w) = Fin.snoc w w₀ := by
    intro w₀ w
    show Fin.insertNthEquiv (fun _ => α) (Fin.last n) (w₀, w) = Fin.snoc w w₀
    rw [Fin.insertNthEquiv_last]
    rfl
  calc _ =
      ∫⁻ p : α × (Fin n → α), density (s := s) (n := n + 1) hT v (e'.symm p)
        ∂(μ.prod (Measure.pi fun _ => μ)) := by
        rw [← hmp'.lintegral_comp_emb e'.symm.measurableEmbedding
          (density (s := s) (n := n + 1) hT v)]
    _ = ∫⁻ w₀, ∫⁻ w,
          density (s := s) (n := n + 1) hT v (Fin.snoc w w₀)
        ∂(Measure.pi fun _ => μ) ∂μ := by
      rw [lintegral_prod (fun p => density (s := s) (n := n + 1) hT v (e'.symm p))
        ((measurable_density (s := s) (n := n + 1) hT (v := v)).comp e'.symm.measurable).aemeasurable]
      congr 1
      ext w₀
      congr 1
      ext w
      rw [heq]
    _ = _ := by
      apply lintegral_congr
      intro w₀
      apply lintegral_congr
      intro w
      rw [density_snoc (s := s) hT v w₀ w]


/--
Chapman–Kolmogorov marginalization of a Markov chain: integrating the initial
density times the product of one-step transition densities over the first `n`
states yields the marginal density of the `n`-th state:

  ∫ ℙ(s₀ = u₀) · ∏_{t<n} ℙ(s_{t+1} = u_{t+1} | s_t = u_t) du₀…du_{n-1} = ℙ(sₙ = v)

Python: Random.Integral_Prod.eq.Prob.
-/
@[path]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α]
  [Countable α] [MeasurableSingletonClass α]
  {π : Measure Ω}
  {s : ℕ → Ω → α}
  {n : ℕ} [SinglePSpace π (s 0)]
-- given
  (hα : ReferenceMeasure.measure (α := α) = Measure.count)
  (hT : ∀ t : ℕ, SinglePSpace π (s (t + 1), s t))
  (v : α) :
-- imply
  have _ : SinglePSpace π (s n) := singlePSpace_s hT
  ∫⁻ u : Fin n → α,
      density (s := s) (n := n) hT v u
    ∂(Measure.pi fun _ => ReferenceMeasure.measure) =
    π.prob (s n) v := by
-- proof
  induction n generalizing v with
  | zero =>
    have hμ :
      (Measure.pi fun _ : Fin 0 => ReferenceMeasure.measure) =
        Measure.dirac (Fin.elim0 : Fin 0 → α) :=
      Measure.pi_of_empty _
    rw [hμ, lintegral_dirac' (Fin.elim0 : Fin 0 → α)
      (@measurable_density Ω α _ _ π s inferInstance 0 hT v)]
    exact density_zero (s := s) hT v
  | succ n ih =>
    let μ := ReferenceMeasure.measure (α := α)
    have hP : SinglePSpace π (s (n + 1), s n) := hT n
    have _ : SinglePSpace π (s n) := singlePSpace_s hT
    have _ : SinglePSpace π (s (n + 1)) := PSpace.of.PSpace_Joint.fst hP
    calc _ =
        ∫⁻ w₀, ∫⁻ w,
            density (s := s) (n := n) hT w₀ w *
              @MeasureTheory.Measure.condProb Ω α α _ _ _ π (s (n + 1), s n) (hT n) (v, w₀)
          ∂(Measure.pi fun _ => μ) ∂μ :=
      lintegral_density_snoc (s := s) hT v
      _ = ∫⁻ w₀,
            (∫⁻ w, density (s := s) (n := n) hT w₀ w ∂(Measure.pi fun _ => μ)) *
              @MeasureTheory.Measure.condProb Ω α α _ _ _ π (s (n + 1), s n) (hT n) (v, w₀)
          ∂μ := by
        apply lintegral_congr
        intro w₀
        rw [lintegral_mul_const'' _
          (measurable_density (s := s) (n := n) hT (v := w₀)).aemeasurable]
      _ = ∫⁻ w₀, π.prob (s n) w₀ *
            @MeasureTheory.Measure.condProb Ω α α _ _ _ π (s (n + 1), s n) (hT n) (v, w₀) ∂μ := by
        apply lintegral_congr
        intro w₀
        rw [ih w₀]
      _ = ∫⁻ w₀, π.prob (s (n + 1), s n) (v, w₀) ∂μ := by
        apply lintegral_congr_ae (mulProbJoint_fst (x := s (n + 1)) (y := s n) hP hα v)
      _ = π.prob (s (n + 1)) v :=
        integral_probJoint_fst (x := s (n + 1)) (y := s n) hP hα v


-- created on 2023-04-04
-- updated on 2026-10-10
