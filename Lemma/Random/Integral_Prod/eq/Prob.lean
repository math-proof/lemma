import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Lemma.Random.All_EqIntegral_ProbJoint.of.PSpace_Joint
import Lemma.Random.All_Eq_MulProbCond.of.PSpace_Joint
import Lemma.Random.PSpace.PSpace.of.PSpace_Joint
import sympy.stats.joint_rv
import sympy.Basic
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
  let path : Fin (n + 1) → α := Fin.snoc u v
  π.prob (s 0) (path 0) *
    ∏ t : Fin n,
      @MeasureTheory.Measure.condProb Ω α α _ _ _ π (s (t.val +  1), s t.val) (hT t.val)
        (path t.succ, path t.castSucc)


private lemma snoc_zero_eval
  {α : Type*} (v : α) (i : Fin 1) :
  (Fin.snoc (Fin.elim0 : Fin 0 → α) v) i = v := by
  fin_cases i
  exact Fin.snoc_last _ _


private lemma density_zero
  [MeasurableSpace Ω]
  [ReferenceMeasure α]
  {π : Measure Ω}
  {s : ℕ → Ω → α}
  [SinglePSpace π (s 0)]
  (hT : ∀ t : ℕ, SinglePSpace π (s (t + 1), s t))
  (v : α) :
  density (s := s) (n := 0) hT v Fin.elim0 = π.prob (s 0) v := by
  simp [density, snoc_zero_eval]


private lemma integral_probJoint_fst
  [MeasurableSpace Ω]
  [ReferenceMeasure α]
  {π : Measure Ω}
  {x : Ω → α} {y : Ω → β}
  [ReferenceMeasure β]
  [SinglePSpace π x]
  (hP : SinglePSpace π (x, y))
  (v : α) :
  ∫⁻ w : β, π.prob (x, y) (v, w) ∂ReferenceMeasure.measure =
    π.prob x v := by
  have hmain := All_EqIntegral_ProbJoint.of.PSpace_Joint hP
  simp at hmain
  have hAt := hmain v
  simp at hAt
  exact hAt


private lemma mulProbJoint_fst
  [MeasurableSpace Ω]
  [ReferenceMeasure α]
  {π : Measure Ω}
  {x : Ω → α} {y : Ω → β}
  [ReferenceMeasure β]
  [SinglePSpace π x]
  (hP : SinglePSpace π (x, y))
  (v : α) :
  (fun w : β =>
      @MeasureTheory.Measure.condProb Ω β β _ _ _ π (x, y) hP (v, w) *
        π.prob y w) =ᵐ[ReferenceMeasure.measure]
    fun w : β => π.prob (x, y) (v, w) := by
  let μ := ReferenceMeasure.measure (α := α)
  let ν := ReferenceMeasure.measure (α := β)
  have hmul := All_Eq_MulProbCond.of.PSpace_Joint hP
  have hprod :
      (fun z : α × β =>
          @MeasureTheory.Measure.condProb Ω β β _ _ _ π (x, y) hP z * π.prob y z.2) =ᵐ[μ.prod ν]
        fun z : α × β => π.prob (x, y) z :=
    (Measure.ae_prod_iff (by fun_prop)).mpr hmul
  refine (Measure.ae_ae_of_ae_prod hprod).mono ?_
  intro w h
  simpa using h v w


private lemma density_snoc
  [MeasurableSpace Ω]
  [ReferenceMeasure α]
  {π : Measure Ω}
  {s : ℕ → Ω → α}
  [SinglePSpace π (s 0)]
  {n : ℕ}
  (hT : ∀ t : ℕ, SinglePSpace π (s (t + 1), s t))
  (v w₀ : α) (w : Fin n → α) :
  density (s := s) (n := n + 1) hT v (Fin.snoc w w₀) =
    density (s := s) (n := n) hT w₀ w *
      @MeasureTheory.Measure.condProb Ω α α _ _ _ π (s (n + 1), s n) (hT n) (v, w₀) := by
  set path' : Fin (n + 1) → α := Fin.snoc w w₀
  set path : Fin (n + 2) → α := Fin.snoc path' v
  have hprod :
      ∏ t : Fin (n + 1),
          @MeasureTheory.Measure.condProb Ω α α _ _ _ π (s (t.val + 1), s t.val) (hT t.val)
            (path t.succ, path t.castSucc) =
        (∏ t : Fin n,
            @MeasureTheory.Measure.condProb Ω α α _ _ _ π (s (t.val + 1), s t.val) (hT t.val)
              (path' t.succ, path' t.castSucc)) *
          @MeasureTheory.Measure.condProb Ω α α _ _ _ π (s (n + 1), s n) (hT n) (v, w₀) := by
    rw [Fin.prod_univ_castSucc]
    simp [path, path', Fin.snoc_castSucc, Fin.snoc_last, Fin.succ_last]
  rw [density, density, hprod]
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
  unfold density
  fun_prop


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
  set e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) (Fin.last n)).symm
  have hmp :
      MeasurePreserving e (μ.prod (Measure.pi fun _ : Fin n => μ)) (Measure.pi fun _ => μ) := by
    simpa [e] using
      (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) (Fin.last n)).symm
  calc
    ∫⁻ u, density (s := s) (n := n + 1) hT v u ∂(Measure.pi fun _ => μ)
        = ∫⁻ p : α × (Fin n → α), density (s := s) (n := n + 1) hT v (e p)
            ∂(μ.prod (Measure.pi fun _ => μ)) := by
          rw [← hmp.lintegral_comp_emb e.measurableEmbedding
            (density (s := s) (n := n + 1) hT v)]
    _ = ∫⁻ w₀, ∫⁻ w,
          density (s := s) (n := n + 1) hT v (Fin.snoc w w₀) *
            @MeasureTheory.Measure.condProb Ω α α _ _ _ π (s (n + 1), s n) (hT n) (v, w₀)
        ∂(Measure.pi fun _ => μ) ∂μ := by
      rw [lintegral_prod (density (s := s) (n := n + 1) hT v ∘ e) (by fun_prop)]
      congr 1
      ext w₀
      apply lintegral_congr
      intro w
      rw [density_snoc (s := s) hT v w₀ w]
      ring_nf


/--
Chapman–Kolmogorov marginalization of a Markov chain: integrating the initial
density times the product of one-step transition densities over the first `n`
states yields the marginal density of the `n`-th state:

  ∫ Pr(s₀ = u₀) · ∏_{t<n} Pr(s_{t+1} = u_{t+1} | s_t = u_t) du₀…du_{n-1} = Pr(sₙ = v)

Python: Random.Integral_Prod.eq.Prob.
-/
@[path]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α]
  {π : Measure Ω}
  {s : ℕ → Ω → α}
  {n : ℕ} [SinglePSpace π (s 0)]
-- given
  (hT : ∀ t : ℕ, SinglePSpace π (s (t + 1), s t))
  (v : α) :
-- imply
  ∫⁻ u : Fin n → α,
      density (s := s) (n := n) hT v u
    ∂(Measure.pi fun _ => ReferenceMeasure.measure) =
    π.prob (s n) v := by
-- proof
  induction n generalizing v with
  | zero =>
    simp [Measure.pi_of_empty, density_zero (s := s) hT v]
  | succ n ih =>
    let μ := ReferenceMeasure.measure (α := α)
    have hP : SinglePSpace π (s (n + 1), s n) := hT n
    have hSn : SinglePSpace π (s n) := PSpace.of.PSpace_Joint.snd hP
    have hS0 : SinglePSpace π (s (n + 1)) := PSpace.of.PSpace_Joint.fst hP
    calc
      ∫⁻ u, density (s := s) (n := n + 1) hT v u ∂(Measure.pi fun _ => μ)
          = ∫⁻ w₀, ∫⁻ w,
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
        have hSn' : SinglePSpace π (s n) := hSn
        rw [ih w₀]
      _ = ∫⁻ w₀, π.prob (s (n + 1), s n) (v, w₀) ∂μ := by
        apply lintegral_congr_ae (mulProbJoint_fst hP v)
      _ = π.prob (s (n + 1)) v :=
        integral_probJoint_fst hP v


-- created on 2026-10-01
