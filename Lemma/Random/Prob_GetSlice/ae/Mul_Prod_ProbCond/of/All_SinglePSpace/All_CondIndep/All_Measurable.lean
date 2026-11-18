import Lemma.Random.Prob_GetSlice.ae.Prod_Prob_Cond.of.All_SinglePSpace.All_SinglePSpace.All_Measurable
import Lemma.Random.All_SinglePSpaceJointGet__GetSlice.All_SinglePSpaceJointGet_Add_1_Get.of.All_SinglePSpaceGetSlice
import Lemma.Random.All_MeasurableGetSlice.of.All_Measurable
import Lemma.Random.All_Imp_EqProbSCond.of.CondIndep
import Lemma.Random.SinglePSpace.SinglePSpace.of.SinglePSpace
import Lemma.Random.Map.eq.WithDensityProb
import Instance.Probability.Process.HiddenMarkovSequence.Part2
import Notation.Probability.JointRv
import Notation.Fun
import Syntax.Probability.Probability
import Initialize.Tactic.Attr.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Independence.Conditional
open MeasureTheory ProbabilityTheory Random Fun
open scoped ProbabilityTheory


/--
The length-1 prefix density agrees with the density of the initial state,
almost surely, by the measure-preserving identification `Fin 1 → 𝒮 ≃ 𝒮`.
-/
private lemma Prob_prefix1
  [MeasurableSpace Ω]
  [ReferenceMeasure 𝒮]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {s : ℕ ⇀ Ω → 𝒮}
-- given
  (hs : ∀ k, Measurable s[k])
  (hP : ∀ n, SinglePSpace π (s[:n] : Ω → Fin n → 𝒮)) :
-- imply
  have : Measurable s[:1] := All_MeasurableGetSlice.of.All_Measurable hs 1
  have : SinglePSpace π (s[:1] : Ω → Fin 1 → 𝒮) := hP 1
  have : SinglePSpace π s[0] :=
    SinglePSpace.of.SinglePSpace.fst (All_SinglePSpaceJointGet__GetSlice.of.All_SinglePSpaceGetSlice hP 0)
  ℙ[π](s[:1]) =ᵐ[π] ℙ[π](s[0]) := by
-- proof
  intro _ hP1 hP0
  let e := MeasurableEquiv.funUnique (Fin 1) 𝒮
  have href :
    ReferenceMeasure.measure (α := Fin 1 → 𝒮) =
      Measure.pi fun _ : Fin 1 => ReferenceMeasure.measure (α := 𝒮) :=
    rfl
  have hmp :
    MeasurePreserving e
      (ReferenceMeasure.measure : Measure (Fin 1 → 𝒮))
      (ReferenceMeasure.measure : Measure 𝒮) := by
    rw [href]
    apply measurePreserving_funUnique
      (ReferenceMeasure.measure : Measure 𝒮) (Fin 1)
  have hfun : s[0] = e ∘ (s[:1] : Ω → Fin 1 → 𝒮) := by
    funext ω
    simp [Fun.getSlice, Function.getSlice, FunSlice.slice, Int.toNat_zero]
    rfl
  have hmap :
    π.map s[0] =
      (π.map (s[:1] : Ω → Fin 1 → 𝒮)).map e := by
    rw [hfun]
    apply Eq.symm
    apply AEMeasurable.map_map_of_aemeasurable e.measurable.aemeasurable
      hP1.aemeasurable
  have habs :
    π.map (s[:1] : Ω → Fin 1 → 𝒮) ≪
      ReferenceMeasure.measure (α := Fin 1 → 𝒮) := by
    obtain ⟨ρ, _, hlaw⟩ := hP1.exists_distribution
    rw [hlaw]
    apply withDensity_absolutelyContinuous
  have hrd :=
    e.measurableEmbedding.rnDeriv_map
      (π.map (s[:1] : Ω → Fin 1 → 𝒮))
      (ReferenceMeasure.measure (α := Fin 1 → 𝒮))
  have hrd' :
    (fun p =>
      (π.map s[0]).rnDeriv ReferenceMeasure.measure (e p)) =ᵐ[ReferenceMeasure.measure (α := Fin 1 → 𝒮)]
      fun p =>
        (π.map (s[:1] : Ω → Fin 1 → 𝒮)).rnDeriv
          ReferenceMeasure.measure p := by
    simpa [hmap, hmp.map_eq] using hrd
  have h1 := ae_of_ae_map hP1.aemeasurable (habs.ae_le hrd')
  filter_upwards [h1] with ω h
  change
    (π.map (s[:1] : Ω → Fin 1 → 𝒮)).rnDeriv ReferenceMeasure.measure
      ((s[:1] : Ω → Fin 1 → 𝒮) ω) =
    (π.map s[0]).rnDeriv ReferenceMeasure.measure (s[0] ω)
  rw [hfun, Function.comp_apply]
  apply h.symm

/--
One-step chain rule for a prefix density:

  \(\mathbb{P}_{\pi}(s[:n+1]) = \mathbb{P}_{\pi}(s[n] \mid s[:n]) \cdot \mathbb{P}_{\pi}(s[:n])\).
-/
private lemma Prob_prefix_succ
  [MeasurableSpace Ω]
  [ReferenceMeasure 𝒮]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {s : ℕ ⇀ Ω → 𝒮}
-- given
  (hs : ∀ k, Measurable s[k])
  (hP : ∀ n, SinglePSpace π (s[:n] : Ω → Fin n → 𝒮))
  (n : ℕ) :
-- imply
  have : ∀ k : ℕ, Measurable s[:k] :=
    All_MeasurableGetSlice.of.All_Measurable hs
  have : SinglePSpace π (s[:n.succ] : Ω → Fin n.succ → 𝒮) := hP n.succ
  have : SinglePSpace π (s[:n] : Ω → Fin n → 𝒮) := hP n
  have : SinglePSpace π (s[n], fun ω => s[:n] ω) := All_SinglePSpaceJointGet__GetSlice.of.All_SinglePSpaceGetSlice hP n
  ℙ[π](s[:n.succ]) =ᵐ[π] ℙ[π](s[n] | s[:n]) * ℙ[π](s[:n]) := by
-- proof
  intro _ _ _ _
  have hsucc :=
    Prob_GetSlice.ae.Prod_Prob_Cond.of.All_SinglePSpace.All_SinglePSpace.All_Measurable hs hP n.succ
  have hpref :=
    Prob_GetSlice.ae.Prod_Prob_Cond.of.All_SinglePSpace.All_SinglePSpace.All_Measurable hs hP n
  filter_upwards [hsucc, hpref] with ω h₁ h₂
  simp only [Finset.prod_range_succ, Pi.mul_apply] at h₁ h₂ ⊢
  rw [h₁, h₂, mul_comm]

/--
The length-`(t + 1)` prefix is the snoc of the length-`t` prefix and the
current state, pointwise.
-/
private lemma getSlice_snoc
  {s : ℕ ⇀ Ω → 𝒮}
-- given
  (t : ℕ) (ω : Ω) :
-- imply
  (s[:t.succ] : Ω → Fin t.succ → 𝒮) ω =
    Fin.snoc ((s[:t] : Ω → Fin t → 𝒮) ω) (s[t] ω) := by
-- proof
  ext i
  refine Fin.lastCases ?_ ?_ i
  · simp [Fun.getSlice, Function.getSlice, FunSlice.slice, Fin.snoc_last,
      Fin.val_last, Int.toNat_natCast]
  ·
    intro j
    simp [Fun.getSlice, Function.getSlice, FunSlice.slice, Fin.snoc_castSucc,
      Int.toNat_natCast]

/--
Under the first-order Markov property, the conditional density of the next
state given the full prefix equals the conditional density given only the
current state, almost surely.
-/
private lemma ProbCond_markov
  [MeasurableSpace Ω] [StandardBorelSpace Ω]
  [ReferenceMeasure 𝒮] [StandardBorelSpace 𝒮] [Nonempty 𝒮]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {s : ℕ ⇀ Ω → 𝒮}
-- given
  (hs : ∀ k, Measurable s[k])
  (hmarkov : ∀ (t : ℕ), s[t + 1] ⟂ᵢ[π] s[:t] | s[t])
  (hP : ∀ n, SinglePSpace π (s[:n] : Ω → Fin n → 𝒮))
  (t : ℕ) :
-- imply
  have : ∀ k : ℕ, Measurable s[:k] :=
    All_MeasurableGetSlice.of.All_Measurable hs
  have : SinglePSpace π (s[t + 1], s[:t.succ]) := All_SinglePSpaceJointGet__GetSlice.of.All_SinglePSpaceGetSlice hP t.succ
  have : SinglePSpace π (s[t + 1], s[t]) := All_SinglePSpaceJointGet_Add_1_Get.of.All_SinglePSpaceGetSlice hP t
  ℙ[π](s[t + 1] | s[:t.succ]) =ᵐ[π] ℙ[π](s[t + 1] | s[t]) := by
-- proof
  intro hs_pref hPstep_succ hPadj_t
  let e_last :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin t.succ => 𝒮) (Fin.last t)
  let e : (Fin t → 𝒮) × 𝒮 ≃ᵐ (Fin t.succ → 𝒮) :=
    ((MeasurableEquiv.prodComm : (Fin t → 𝒮) × 𝒮 ≃ᵐ 𝒮 × (Fin t → 𝒮))).trans e_last.symm
  have href_pi (n : ℕ) :
    ReferenceMeasure.measure (α := Fin n → 𝒮) =
      Measure.pi fun _ : Fin n => ReferenceMeasure.measure (α := 𝒮) :=
    rfl
  have href_left :
    ReferenceMeasure.measure (α := (Fin t → 𝒮) × 𝒮) =
      (ReferenceMeasure.measure (α := Fin t → 𝒮)).prod
        (ReferenceMeasure.measure (α := 𝒮)) :=
    rfl
  have href_right :
    ReferenceMeasure.measure (α := 𝒮 × (Fin t → 𝒮)) =
      (ReferenceMeasure.measure (α := 𝒮)).prod
        (ReferenceMeasure.measure (α := Fin t → 𝒮)) :=
    rfl
  have hmp_swap :
    MeasurePreserving ((MeasurableEquiv.prodComm : (Fin t → 𝒮) × 𝒮 ≃ᵐ 𝒮 × (Fin t → 𝒮)))
      (ReferenceMeasure.measure : Measure ((Fin t → 𝒮) × 𝒮))
      (ReferenceMeasure.measure : Measure (𝒮 × (Fin t → 𝒮))) := by
    refine ⟨((MeasurableEquiv.prodComm : (Fin t → 𝒮) × 𝒮 ≃ᵐ 𝒮 × (Fin t → 𝒮))).measurable, ?_⟩
    rw [href_left, href_right]
    apply Measure.prod_swap
      (μ := ReferenceMeasure.measure (α := Fin t → 𝒮))
      (ν := ReferenceMeasure.measure (α := 𝒮))
  have hmp_last :
    MeasurePreserving e_last.symm
      (ReferenceMeasure.measure : Measure (𝒮 × (Fin t → 𝒮)))
      (ReferenceMeasure.measure : Measure (Fin t.succ → 𝒮)) := by
    rw [href_right, href_pi t, href_pi t.succ]
    exact (measurePreserving_piFinSuccAbove
      (fun _ : Fin t.succ => ReferenceMeasure.measure (α := 𝒮))
      (Fin.last t)).symm
  have hmp : MeasurePreserving e
    (ReferenceMeasure.measure : Measure ((Fin t → 𝒮) × 𝒮))
    (ReferenceMeasure.measure : Measure (Fin t.succ → 𝒮)) :=
    hmp_swap.trans hmp_last
  have he_snoc (f : Fin t → 𝒮) (x : 𝒮) : e (f, x) = Fin.snoc f x := by
    change e_last.symm (x, f) = Fin.snoc f x
    exact Fin.insertNth_last' x f
  have hfun :
    (s[:t.succ] : Ω → Fin t.succ → 𝒮) =
      e ∘ fun ω => ((s[:t] : Ω → Fin t → 𝒮) ω, s[t] ω) := by
    funext ω
    rw [Function.comp_apply, he_snoc, getSlice_snoc]
  let W : Ω → (Fin t → 𝒮) × 𝒮 :=
    fun ω => ((s[:t] : Ω → Fin t → 𝒮) ω, s[t] ω)
  let Y : Ω → Fin t.succ → 𝒮 := (s[:t.succ] : Ω → Fin t.succ → 𝒮)
  let X : Ω → 𝒮 := s[t + 1]
  have hfunY : Y = e ∘ W := hfun
  have hfunXY :
    (X, Y) =
      Prod.map (id : 𝒮 → 𝒮) (e : (Fin t → 𝒮) × 𝒮 → Fin t.succ → 𝒮) ∘
        (X, W) := by
    funext ω
    simp [JointRandomSymbol, hfunY]
  let eXY := MeasurableEquiv.prodCongr (MeasurableEquiv.refl 𝒮) e
  have hfunXY' :
    (X, W) = eXY.symm ∘ (X, Y) := by
    funext ω
    change (X ω, W ω) = eXY.symm (X ω, Y ω)
    have hY : Y ω = e (W ω) := congrFun hfunY ω
    rw [hY]
    have hxy : eXY.symm (X ω, e (W ω)) = (X ω, e.symm (e (W ω))) := rfl
    rw [hxy, MeasurableEquiv.symm_apply_apply]
  have hXY : SinglePSpace π (X, Y) := hPstep_succ
  have heXY :
    MeasurePreserving eXY
      (ReferenceMeasure.measure : Measure (𝒮 × ((Fin t → 𝒮) × 𝒮)))
      (ReferenceMeasure.measure : Measure (𝒮 × (Fin t.succ → 𝒮))) := by
    change MeasurePreserving _
      ((ReferenceMeasure.measure (α := 𝒮)).prod
        (ReferenceMeasure.measure (α := (Fin t → 𝒮) × 𝒮)))
      ((ReferenceMeasure.measure (α := 𝒮)).prod
        (ReferenceMeasure.measure (α := Fin t.succ → 𝒮)))
    exact (MeasurePreserving.id (ReferenceMeasure.measure (α := 𝒮))).prod hmp
  have heXY_symm : MeasurePreserving eXY.symm
    (ReferenceMeasure.measure : Measure (𝒮 × (Fin t.succ → 𝒮)))
    (ReferenceMeasure.measure : Measure (𝒮 × ((Fin t → 𝒮) × 𝒮))) :=
    heXY.symm
  have hXW : SinglePSpace π (X, W) := by
    obtain ⟨ρ, hρ, hlaw⟩ := hXY.exists_distribution
    let ρ' : 𝒮 × ((Fin t → 𝒮) × 𝒮) → ENNReal := ρ ∘ eXY
    have hρ' : Measurable ρ' := hρ.comp eXY.measurable
    refine {
      toIsProbabilityMeasure := inferInstance
      aemeasurable := ?_
      exists_distribution := ⟨ρ', hρ', ?_⟩
    }
    ·
      rw [hfunXY']
      exact eXY.symm.measurable.comp_aemeasurable hXY.aemeasurable
    ·
      have hmap :
        π.map (X, W) =
          (π.map (X, Y)).map eXY.symm := by
        rw [hfunXY']
        exact (AEMeasurable.map_map_of_aemeasurable
          eXY.symm.measurable.aemeasurable hXY.aemeasurable).symm
      rw [hmap, hlaw]
      have hwd :
        ((ReferenceMeasure.measure
            (α := 𝒮 × (Fin t.succ → 𝒮))).withDensity ρ).map eXY.symm =
          ((ReferenceMeasure.measure
              (α := 𝒮 × (Fin t.succ → 𝒮))).map eXY.symm).withDensity
            (ρ ∘ eXY) := by
        ext s hs
        rw [Measure.map_apply eXY.symm.measurable hs,
          withDensity_apply _ (eXY.symm.measurable hs),
          withDensity_apply _ hs,
          setLIntegral_map hs (hρ.comp eXY.measurable) eXY.symm.measurable]
        refine setLIntegral_congr_fun (eXY.symm.measurable hs) ?_
        intro x hx
        simp
      simpa [ρ', heXY_symm.map_eq] using hwd
  have hW : SinglePSpace π W := SinglePSpace.of.SinglePSpace.snd hXW
  have hYsp : SinglePSpace π Y := SinglePSpace.of.SinglePSpace.snd hXY
  have hident : ℙ[π](X | Y) =ᵐ[π] ℙ[π](X | W) := by
    have hfemb := e.measurableEmbedding
    have hfembXY :
      MeasurableEmbedding
        (Prod.map (id : 𝒮 → 𝒮) (e : (Fin t → 𝒮) × 𝒮 → Fin t.succ → 𝒮)) :=
      MeasurableEmbedding.id.prodMap hfemb
    have habsW :
      π.map W ≪ ReferenceMeasure.measure (α := (Fin t → 𝒮) × 𝒮) := by
      obtain ⟨ρ, _, hlaw⟩ := hW.exists_distribution
      rw [hlaw]
      exact withDensity_absolutelyContinuous _ _
    have habsXW :
      π.map (X, W) ≪
        ReferenceMeasure.measure (α := 𝒮 × ((Fin t → 𝒮) × 𝒮)) := by
      obtain ⟨ρ, _, hlaw⟩ := hXW.exists_distribution
      rw [hlaw]
      exact withDensity_absolutelyContinuous _ _
    have hmapY : π.map Y = (π.map W).map e := by
      rw [hfunY]
      exact (AEMeasurable.map_map_of_aemeasurable
        e.measurable.aemeasurable hW.aemeasurable).symm
    have hmapXY :
      π.map (X, Y) =
        (π.map (X, W)).map (Prod.map id e) := by
      rw [hfunXY]
      exact (AEMeasurable.map_map_of_aemeasurable
        (measurable_id.prodMap e.measurable).aemeasurable
        hXW.aemeasurable).symm
    have hrefXY :
      ReferenceMeasure.measure (α := 𝒮 × (Fin t.succ → 𝒮)) =
        (ReferenceMeasure.measure (α := 𝒮 × ((Fin t → 𝒮) × 𝒮))).map
          (Prod.map id e) :=
      heXY.map_eq.symm
    have hrd_den :=
      hfemb.rnDeriv_map (π.map W)
        (ReferenceMeasure.measure (α := (Fin t → 𝒮) × 𝒮))
    have hrd_num :=
      hfembXY.rnDeriv_map (π.map (X, W))
        (ReferenceMeasure.measure (α := 𝒮 × ((Fin t → 𝒮) × 𝒮)))
    have hden :
      (fun ω => (π.map Y).rnDeriv ReferenceMeasure.measure (Y ω)) =ᵐ[π]
        fun ω => (π.map W).rnDeriv ReferenceMeasure.measure (W ω) := by
      have hrd_den' :
        (fun p => (π.map Y).rnDeriv ReferenceMeasure.measure (e p)) =ᵐ[ReferenceMeasure.measure (α := (Fin t → 𝒮) × 𝒮)]
          fun p => (π.map W).rnDeriv ReferenceMeasure.measure p := by
        simpa [hmapY, hmp.map_eq] using hrd_den
      have h := ae_of_ae_map hW.aemeasurable (habsW.ae_le hrd_den')
      filter_upwards [h] with ω hω
      have : Y ω = e (W ω) := congrFun hfunY ω
      simpa [this] using hω
    have hnum :
      (fun ω => (π.map (X, Y)).rnDeriv
        ReferenceMeasure.measure (X ω, Y ω)) =ᵐ[π]
        fun ω => (π.map (X, W)).rnDeriv
          ReferenceMeasure.measure (X ω, W ω) := by
      have hrd_num' :
        (fun p => (π.map (X, Y)).rnDeriv
          ReferenceMeasure.measure (Prod.map id e p)) =ᵐ[ReferenceMeasure.measure (α := 𝒮 × ((Fin t → 𝒮) × 𝒮))]
          fun p => (π.map (X, W)).rnDeriv
            ReferenceMeasure.measure p := by
        simpa [hmapXY, hrefXY] using hrd_num
      have h := ae_of_ae_map hXW.aemeasurable (habsXW.ae_le hrd_num')
      filter_upwards [h] with ω hω
      have hY : Y ω = e (W ω) := congrFun hfunY ω
      rwa [hY]
    filter_upwards [hnum, hden] with ω hn hd
    change π.condProb (X, Y) (X ω, Y ω) = π.condProb (X, W) (X ω, W ω)
    simp [Measure.condProb, Measure.prob]
    have hsndY : (fun ω => ((X, Y) ω).2) = Y := rfl
    have hsndW : (fun ω => ((X, W) ω).2) = W := rfl
    rw [hsndY, hsndW, hn, hd]
  have hpoint :=
    All_Imp_EqProbSCond.of.CondIndep
      (hs (t + 1)) (hs_pref t) (hs t) hXW (hmarkov t)
  have hPyz : SinglePSpace π W := hW
  have hpyz_ne : ∀ᵐ ω ∂π, π.prob W (W ω) ≠ 0 := by
    have hlaw : π.map W =
        (ReferenceMeasure.measure (α := (Fin t → 𝒮) × 𝒮)).withDensity
          (π.prob W) :=
      Map.eq.WithDensityProb
    have hρm : Measurable (π.prob W) := Measure.measurable_rnDeriv _ _
    have hset : MeasurableSet {p | π.prob W p = 0} :=
      hρm (measurableSet_singleton 0)
    have h0 : (π.map W) {p | π.prob W p = 0} = 0 := by
      rw [hlaw, withDensity_apply _ hset]
      refine setLIntegral_eq_zero hset ?_
      intro p hp
      simp at hp
      simp [hp]
    have hW_m : AEMeasurable W π := hW.aemeasurable
    have hnull : π {ω | π.prob W (W ω) = 0} = 0 := by
      have hpre :
        W ⁻¹' {p | π.prob W p = 0} = {ω | π.prob W (W ω) = 0} := rfl
      rw [Measure.map_apply_of_aemeasurable hW_m hset] at h0
      simpa [hpre] using h0
    simpa [ae_iff] using hnull
  let μref :=
    (ReferenceMeasure.measure (α := 𝒮)).prod
      ((ReferenceMeasure.measure (α := Fin t → 𝒮)).prod
        (ReferenceMeasure.measure (α := 𝒮)))
  have hprod :
    ∀ᵐ p ∂μref,
      π.prob W p.2 ≠ 0 →
        π.condProb (X, W) p = π.condProb (X, s[t]) (p.1, p.2.2) := by
    have hset : MeasurableSet
      {p : 𝒮 × ((Fin t → 𝒮) × 𝒮) |
        π.prob W p.2 ≠ 0 →
          π.condProb (X, W) p = π.condProb (X, s[t]) (p.1, p.2.2)} := by
      have hρW : Measurable (π.prob W) := Measure.measurable_rnDeriv _ _
      have hcw : Measurable (π.condProb (X, W)) := by
        unfold Measure.condProb Measure.prob
        fun_prop
      have hcz : Measurable fun p : 𝒮 × ((Fin t → 𝒮) × 𝒮) =>
          π.condProb (X, s[t]) (p.1, p.2.2) := by
        unfold Measure.condProb Measure.prob
        fun_prop
      exact MeasurableSet.imp
        ((measurableSet_singleton (0 : ENNReal)).preimage
          (hρW.comp measurable_snd)).compl
        (measurableSet_eq_fun hcw hcz)
    rw [Measure.ae_prod_iff_ae_ae hset]
    filter_upwards [hpoint] with x hx
    have hset2 : MeasurableSet
      {q : (Fin t → 𝒮) × 𝒮 |
        π.prob W q ≠ 0 →
          π.condProb (X, W) (x, q) = π.condProb (X, s[t]) (x, q.2)} := by
      have hρW : Measurable (π.prob W) := Measure.measurable_rnDeriv _ _
      have hcw : Measurable fun q : (Fin t → 𝒮) × 𝒮 =>
          π.condProb (X, W) (x, q) := by
        unfold Measure.condProb Measure.prob
        fun_prop
      have hcz : Measurable fun q : (Fin t → 𝒮) × 𝒮 =>
          π.condProb (X, s[t]) (x, q.2) := by
        unfold Measure.condProb Measure.prob
        fun_prop
      exact MeasurableSet.imp
        ((measurableSet_singleton (0 : ENNReal)).preimage hρW).compl
        (measurableSet_eq_fun hcw hcz)
    rwa [Measure.ae_prod_iff_ae_ae hset2]
  have habs_xyz :
    π.map (X, W) ≪ μref := by
    obtain ⟨ρ, _, hlaw⟩ := hXW.exists_distribution
    have href :
      ReferenceMeasure.measure (α := 𝒮 × ((Fin t → 𝒮) × 𝒮)) =
        (ReferenceMeasure.measure (α := 𝒮)).prod
          ((ReferenceMeasure.measure (α := Fin t → 𝒮)).prod
            (ReferenceMeasure.measure (α := 𝒮))) :=
      rfl
    rw [hlaw, href]
    exact withDensity_absolutelyContinuous _ _
  have halong :
    ∀ᵐ ω ∂π,
      π.prob W (W ω) ≠ 0 →
        π.condProb (X, W) (X ω, W ω) =
          π.condProb (X, s[t]) (X ω, (W ω).2) := by
    have h := ae_of_ae_map hXW.aemeasurable (habs_xyz.ae_le hprod)
    filter_upwards [h] with ω hω
    simpa [JointRandomSymbol] using hω
  have hmark : ℙ[π](X | W) =ᵐ[π] ℙ[π](X | s[t]) := by
    filter_upwards [halong, hpyz_ne] with ω hQ hne
    have := hQ hne
    change π.condProb (X, W) (X ω, W ω) = π.condProb (X, s[t]) (X ω, s[t] ω)
    simpa [W] using this
  filter_upwards [hident, hmark] with ω h₁ h₂
  exact h₁.trans h₂

/--
Markov factorization of a process prefix. If the process satisfies the
first-order Markov property `s[t + 1] ⟂ᵢ[π] s[:t] | s[t]` at every time, then
the chain rule
[prefix density as a product of conditionals on the full past](?module=Random.Prob_GetSlice.ae.Prod_Prob_Cond.of.All_SinglePSpace.All_SinglePSpace.All_Measurable)
collapses to conditionals on the previous state only:

  \(\mathbb{P}_{\pi}(s[:n+1]) = \mathbb{P}_{\pi}(s[0]) \prod_{k<n} \mathbb{P}_{\pi}(s[k+1] \mid s[k])\).

The identity holds almost surely with respect to \(\pi\), as a product of
random-argument densities.
-/
@[path]
private lemma main
  [MeasurableSpace Ω] [StandardBorelSpace Ω]
  [ReferenceMeasure 𝒮] [StandardBorelSpace 𝒮] [Nonempty 𝒮]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {s : ℕ ⇀ Ω → 𝒮}
-- given
  (hs : ∀ k, Measurable s[k])
  (hmarkov : ∀ (t : ℕ), s[t + 1] ⟂ᵢ[π] s[:t] | s[t])
  (hP : ∀ n, SinglePSpace π (s[:n] : Ω → Fin n → 𝒮))
  (n : ℕ) :
-- imply
  have : ∀ k : ℕ, Measurable s[:k] :=
    All_MeasurableGetSlice.of.All_Measurable hs
  have : SinglePSpace π (s[:n.succ] : Ω → Fin n.succ → 𝒮) := hP n.succ
  have : SinglePSpace π s[0] :=
    SinglePSpace.of.SinglePSpace.fst (All_SinglePSpaceJointGet__GetSlice.of.All_SinglePSpaceGetSlice hP 0)
  have : ∀ k, SinglePSpace π (s[k + 1], s[k]) := All_SinglePSpaceJointGet_Add_1_Get.of.All_SinglePSpaceGetSlice hP
  ℙ[π](s[:n.succ]) =ᵐ[π]
    ℙ[π](s[0]) * ∏ k ∈ Finset.range n, ℙ[π](s[k + 1] | s[k]) := by
-- proof
  intro _ _ _ _
  induction n with
  | zero =>
    have h1 := Prob_prefix1 hs hP
    filter_upwards [h1] with ω h
    simp [Pi.mul_apply, mul_one]
    convert h
  | succ m ih =>
    have hstep :=
      Prob_prefix_succ hs hP m.succ
    have hmark :=
      ProbCond_markov hs hmarkov hP m
    have ih' := ih
    filter_upwards [hstep, hmark, ih'] with ω h₁ h₂ h₃
    simp only [Finset.prod_range_succ, Pi.mul_apply] at h₁ h₂ h₃ ⊢
    rw [h₁, h₂, h₃]
    ac_rfl


-- created on 2026-11-18
