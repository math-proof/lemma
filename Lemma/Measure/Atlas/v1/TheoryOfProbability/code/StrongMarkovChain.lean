import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.TheoryOfProbability.code.StrongMarkovChain
open MeasureTheory ProbabilityTheory


/--
[stoppedPathShift_eq_shiftPath_on_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/StrongMarkovChain.lean)
-/
@[path]
lemma stoppedPathShift_eq_shiftPath_on_eq
  {T : (ℕ → S) → ℕ}
  {n : ℕ}
  {ω : ℕ → S}
-- given
  (h : T ω = n) :
-- imply
  stoppedPathShift T ω = shiftPath n ω := by
-- proof
  ext k
  simp [stoppedPathShift, shiftPath, h]

/--
[ae_eq_of_ae_eq_restrict_fibers](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/StrongMarkovChain.lean)
-/
@[path]
lemma ae_eq_of_ae_eq_restrict_fibers
  {m0 : MeasurableSpace Ω}
  {T : Ω → ℕ}
  {μ : @Measure Ω m0}
  {f g : Ω → ℝ}
-- given
  (hT_meas : ∀ n, MeasurableSet {ω : Ω | T ω = n})
  (h : ∀ n, f =ᵐ[μ.restrict {ω | T ω = n}] g) :
-- imply
  f =ᵐ[μ] g := by
-- proof
  have hfiber : ∀ n, ∀ᵐ ω ∂μ, T ω = n → f ω = g ω := by
    intro n
    have hn := h n
    rwa [Filter.EventuallyEq, ae_restrict_iff' (hT_meas n)] at hn
  suffices ∀ᵐ ω ∂μ, ∀ n, T ω = n → f ω = g ω by
    filter_upwards [this] with ω hω
    exact hω (T ω) rfl
  rwa [ae_all_iff]

/--
[strong_markov_chain](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/StrongMarkovChain.lean)
-/
@[path]
lemma strong_markov_chain
  {S : Type*}
  [MeasurableSpace S]
  [StandardBorelSpace S]
  [Nonempty S]
  {μ : Measure S}
  [IsFiniteMeasure μ]
  {κ : Kernel S S}
  [IsMarkovKernel κ]
  {T : (ℕ → S) → ℕ}
  {Y : ℕ → (ℕ → S) → ℝ}
-- given
  (hT : @IsStoppingTime (ℕ → S) ℕ MeasurableSpace.pi _ (pathFiltration S) (fun ω => (T ω : WithTop ℕ)))
  (hY_meas : ∀ n, @Measurable _ _ MeasurableSpace.pi _ (Y n))
  (hY_bdd : ∃ C : ℝ, ∀ n ω, |Y n ω| ≤ C) :
-- imply
  let P_μ := MarkovChainPathMeasure S μ κ @condExp (ℕ → S) ℝ hT.measurableSpace MeasurableSpace.pi _ _ _ P_μ (fun ω => Y (T ω) (stoppedPathShift T ω)) =ᵐ[P_μ] fun ω => markovExpectation S κ (Y (T ω)) (ω (T ω)) := by
-- proof
  intro P_μ
  haveI : @IsFiniteMeasure (ℕ → S) MeasurableSpace.pi P_μ :=
    MarkovChainPathMeasure.isFiniteMeasure S μ κ
  haveI hSF : @SigmaFiniteFiltration (ℕ → S) ℕ MeasurableSpace.pi _
    P_μ (pathFiltration S) := by
    constructor; intro i
    haveI : IsFiniteMeasure (P_μ.trim ((pathFiltration S).le i)) :=
      isFiniteMeasure_trim ((pathFiltration S).le i)
    infer_instance
  haveI hSFT : @SigmaFinite (ℕ → S) hT.measurableSpace
    (P_μ.trim hT.measurableSpace_le) := by
    haveI : IsFiniteMeasure (P_μ.trim hT.measurableSpace_le) :=
      isFiniteMeasure_trim hT.measurableSpace_le
    infer_instance
  have hT_fiber_meas : ∀ n, @MeasurableSet (ℕ → S) MeasurableSpace.pi {ω | T ω = n} := by
    intro n
    have h := hT.measurableSet_eq n
    have heq : {ω : ℕ → S | T ω = n} = {ω | (T ω : WithTop ℕ) = ↑n} := by
      ext ω; simp only [Set.mem_setOf_eq, Nat.cast_inj]
    rw [heq]
    exact (pathFiltration S).le n _ h
  apply ae_eq_of_ae_eq_restrict_fibers T P_μ _ _ hT_fiber_meas
  intro n
  have hstep1 :
    @condExp (ℕ → S) ℝ hT.measurableSpace
      MeasurableSpace.pi _ _ _ P_μ (fun ω => Y (T ω) (stoppedPathShift T ω))
    =ᵐ[P_μ.restrict {ω | T ω = n}]
    @condExp (ℕ → S) ℝ (pathFiltration S n)
      MeasurableSpace.pi _ _ _ P_μ (fun ω => Y (T ω) (stoppedPathShift T ω)) := by
    have hset : {x : ℕ → S | (fun ω => (T ω : WithTop ℕ)) x = ↑n} = {ω | T ω = n} := by
      ext ω; simp [Nat.cast_inj]
    rwa [← hset]
      (ℕ → S) ℕ MeasurableSpace.pi _ P_μ (pathFiltration S)
      (fun ω => (T ω : WithTop ℕ)) ℝ _ _ _ _ _ hSF hT hSFT n
  have hstep2 :
    @condExp (ℕ → S) ℝ (pathFiltration S n)
      MeasurableSpace.pi _ _ _ P_μ (fun ω => Y (T ω) (stoppedPathShift T ω))
    =ᵐ[P_μ.restrict {ω | T ω = n}]
    @condExp (ℕ → S) ℝ (pathFiltration S n)
      MeasurableSpace.pi _ _ _ P_μ (Y n ∘ shiftPath n) := by
    have hs_Fn : @MeasurableSet (ℕ → S) (pathFiltration S n) {ω | T ω = n} := by
      have h := hT.measurableSet_eq n
      have heq : {ω : ℕ → S | T ω = n} = {ω | (T ω : WithTop ℕ) = ↑n} := by
        ext ω; simp only [Set.mem_setOf_eq, Nat.cast_inj]
      rw [heq]; exact h
    obtain ⟨C, hC⟩ := hY_bdd
    have hf_meas : @Measurable (ℕ → S) ℝ MeasurableSpace.pi _
      (fun ω => Y (T ω) (stoppedPathShift T ω)) := by
      intro A hA
      have : (fun ω => Y (T ω) (stoppedPathShift T ω)) ⁻¹' A =
        ⋃ k, {ω | T ω = k} ∩ ((Y k ∘ shiftPath k) ⁻¹' A) := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff,
          Set.mem_setOf_eq, Function.comp]
        constructor
        · intro h; exact ⟨T ω, rfl, h⟩
        · rintro ⟨k, hk, hgk⟩
          rw [show stoppedPathShift T ω = shiftPath k ω from
            stoppedPathShift_eq_shiftPath_on_eq T k ω hk, hk]
          exact hgk
      rw [this]
      exact MeasurableSet.iUnion (fun k =>
        (hT_fiber_meas k).inter (((hY_meas k).comp (measurable_shiftPath k)) hA))
    have hf_int : Integrable (fun ω => Y (T ω) (stoppedPathShift T ω)) P_μ :=
      Integrable.of_bound hf_meas.aestronglyMeasurable C
        (ae_of_all P_μ (fun ω => by rw [Real.norm_eq_abs]; exact hC (T ω) (stoppedPathShift T ω)))
    have hg_int : Integrable (Y n ∘ shiftPath n) P_μ :=
      Integrable.of_bound ((hY_meas n).comp (measurable_shiftPath n)).aestronglyMeasurable C
        (ae_of_all P_μ (fun ω => by rw [Real.norm_eq_abs]; exact hC n (shiftPath n ω)))
    have hagree : ∀ ω : ℕ → S, ω ∈ {ω | T ω = n} →
      Y (T ω) (stoppedPathShift T ω) = (Y n ∘ shiftPath n) ω := by
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω
      simp only [Function.comp, hω]
      congr 1
      exact stoppedPathShift_eq_shiftPath_on_eq T n ω hω
    have hind : ({ω | T ω = n} : Set (ℕ → S)).indicator
      (fun ω => Y (T ω) (stoppedPathShift T ω)) =
      ({ω | T ω = n} : Set (ℕ → S)).indicator (Y n ∘ shiftPath n) := by
      ext ω; simp only [Set.indicator]; split_ifs with h
      · exact hagree ω h
      · rfl
    have h1 := @condExp_indicator (ℕ → S) ℝ (pathFiltration S n) MeasurableSpace.pi
      _ _ _ P_μ (fun ω => Y (T ω) (stoppedPathShift T ω)) {ω | T ω = n} hf_int hs_Fn
    have h2 := @condExp_indicator (ℕ → S) ℝ (pathFiltration S n) MeasurableSpace.pi
      _ _ _ P_μ (Y n ∘ shiftPath n) {ω | T ω = n} hg_int hs_Fn
    have h3 : @condExp (ℕ → S) ℝ (pathFiltration S n) MeasurableSpace.pi _ _ _ P_μ
      (({ω | T ω = n} : Set (ℕ → S)).indicator (fun ω => Y (T ω) (stoppedPathShift T ω)))
      =ᵐ[P_μ]
      @condExp (ℕ → S) ℝ (pathFiltration S n) MeasurableSpace.pi _ _ _ P_μ
        (({ω | T ω = n} : Set (ℕ → S)).indicator (Y n ∘ shiftPath n)) := by rw [hind]
    have h4 : ({ω | T ω = n} : Set (ℕ → S)).indicator
      (@condExp (ℕ → S) ℝ (pathFiltration S n) MeasurableSpace.pi _ _ _ P_μ
        (fun ω => Y (T ω) (stoppedPathShift T ω)))
      =ᵐ[P_μ]
      ({ω | T ω = n} : Set (ℕ → S)).indicator
        (@condExp (ℕ → S) ℝ (pathFiltration S n) MeasurableSpace.pi _ _ _ P_μ
          (Y n ∘ shiftPath n)) :=
      h1.symm.trans (h3.trans h2)
    rw [Filter.EventuallyEq, ae_restrict_iff' (hT_fiber_meas n)]
    filter_upwards [h4] with ω hω hωs
    simp [hωs] at hω
    exact hω
  have hstep3 :
    @condExp (ℕ → S) ℝ (pathFiltration S n)
      MeasurableSpace.pi _ _ _ P_μ (Y n ∘ shiftPath n)
    =ᵐ[P_μ]
      fun ω => markovExpectation S κ (Y n) (ω n) :=
    markov_property_full S μ κ (Y n) (hY_meas n)
      (by obtain ⟨C, hC⟩ := hY_bdd; exact ⟨C, fun ω => hC n ω⟩) n
  have hstep4 :
    (fun ω => markovExpectation S κ (Y n) (ω n))
    =ᵐ[P_μ.restrict {ω | T ω = n}]
    (fun ω => markovExpectation S κ (Y (T ω)) (ω (T ω))) := by
    rw [Filter.EventuallyEq, ae_restrict_iff' (hT_fiber_meas n)]
    filter_upwards with ω hωn
    rw [hωn]
  exact hstep1.trans
    (hstep2.trans (Filter.EventuallyEq.trans (ae_restrict_of_ae hstep3) hstep4))


-- created on 2026-10-23
