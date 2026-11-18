import Lemma.Random.Prob_Cond.ae.Prod_Prob_Cond_Joint.of.Measurable.All_Measurable
import Lemma.Random.All_MeasurableGetSlice.of.All_Measurable
import Lemma.Random.PSpace_JointJoint.is.PSpace_Joint_Joint
import Lemma.Random.SinglePSpace.SinglePSpace.of.SinglePSpace
import Lemma.Random.All_SinglePSpaceJointGet__GetSlice.All_SinglePSpaceJointGet_Add_1_Get.of.All_SinglePSpaceGetSlice
import Instance.Probability.Process.HiddenMarkovSequence.Part2
import Syntax.Probability.Probability
import Notation.Fun
import Initialize.Tactic.Attr.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.Prod
open MeasureTheory ProbabilityTheory Random Fun


/--
Lift a `SinglePSpace` hypothesis along a constant dummy coordinate in
`Fin 0 → 𝒮`.
-/
private lemma SinglePSpace_prod_elim0
  [MeasurableSpace Ω]
  [ReferenceMeasure 𝒮]
  [ReferenceMeasure α]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {X : Ω → α}
  {Z : Ω → Fin 0 → 𝒮}
-- given
  (hX : SinglePSpace π X)
  (hZ : Z = fun _ => Fin.elim0) :
-- imply
  SinglePSpace π (X, Z) := by
-- proof
  let u0 : Fin 0 → 𝒮 := Fin.elim0
  have hZω (ω : Ω) : Z ω = u0 := by rw [hZ]
  have hμ0 :
    ReferenceMeasure.measure (α := Fin 0 → 𝒮) = Measure.dirac u0 := by
    change Measure.pi (fun _ : Fin 0 => ReferenceMeasure.measure (α := 𝒮)) =
      Measure.dirac u0
    exact Measure.pi_of_empty _ u0
  have href :
    ReferenceMeasure.measure (α := α × (Fin 0 → 𝒮)) =
      (ReferenceMeasure.measure (α := α)).map (fun a => (a, u0)) := by
    change
      (ReferenceMeasure.measure (α := α)).prod
        (ReferenceMeasure.measure (α := Fin 0 → 𝒮)) = _
    rw [hμ0, Measure.prod_dirac]
  have hfun : (fun ω => (X ω, Z ω)) = (fun a => (a, u0)) ∘ X := by
    funext ω
    exact Prod.ext rfl (hZω ω)
  have hX_ae : AEMeasurable X π := hX.aemeasurable
  have hpair_ae : AEMeasurable (fun ω => (X ω, Z ω)) π := by
    rw [hfun]
    exact measurable_prodMk_right.comp_aemeasurable hX_ae
  obtain ⟨ρ, hρm, hlaw⟩ := hX.exists_distribution
  let ρ' : α × (Fin 0 → 𝒮) → ENNReal := fun p => ρ p.1
  have hρ'm : Measurable ρ' := hρm.comp measurable_fst
  have hmap :
    π.map (fun ω => (X ω, Z ω)) = (π.map X).map (fun a => (a, u0)) := by
    rw [hfun]
    exact (AEMeasurable.map_map_of_aemeasurable
      measurable_prodMk_right.aemeasurable hX_ae).symm
  have hwd :
    ((ReferenceMeasure.measure (α := α)).withDensity ρ).map (fun a => (a, u0)) =
      ((ReferenceMeasure.measure (α := α)).map (fun a => (a, u0))).withDensity
        ρ' := by
    ext s hs
    rw [Measure.map_apply measurable_prodMk_right hs,
      withDensity_apply _ (measurable_prodMk_right hs),
      withDensity_apply _ hs,
      setLIntegral_map hs hρ'm measurable_prodMk_right]
  refine {
    toIsProbabilityMeasure := inferInstance
    aemeasurable := ?_
    exists_distribution := ⟨ρ', hρ'm, ?_⟩
  }
  ·
    have heq :
      JointRandomSymbol (X, Z).1 (X, Z).2 = fun ω => (X ω, Z ω) := by
      funext ω
      apply Prod.ext
      · rfl
      · rfl
    rwa [heq]
  ·
    change π.map (X, Z) = ReferenceMeasure.measure.withDensity ρ'
    have hmap' : π.map (X, Z) = π.map (fun ω => (X ω, Z ω)) := rfl
    rw [hmap', hmap, hlaw, hwd, href]

/--
Conditioning a random variable on a constant dummy coordinate in
`Fin 0 → 𝒮` does not change its random-argument density, almost surely.
-/
private lemma ProbCond_elim0
  [MeasurableSpace Ω]
  [ReferenceMeasure 𝒮]
  [ReferenceMeasure α]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {X : Ω → α}
  {Z : Ω → Fin 0 → 𝒮}
-- given
  (hX : SinglePSpace π X)
  (hZ : Z = fun _ => Fin.elim0)
  (hXZ : SinglePSpace π (X, Z)) :
-- imply
  ℙ[π](X | Z) =ᵐ[π] ℙ[π](X) := by
-- proof
  let u0 : Fin 0 → 𝒮 := Fin.elim0
  have hZω (ω : Ω) : Z ω = u0 := by rw [hZ]
  have hμ0 :
    ReferenceMeasure.measure (α := Fin 0 → 𝒮) = Measure.dirac u0 := by
    change Measure.pi (fun _ : Fin 0 => ReferenceMeasure.measure (α := 𝒮)) =
      Measure.dirac u0
    exact Measure.pi_of_empty _ u0
  have href :
    ReferenceMeasure.measure (α := α × (Fin 0 → 𝒮)) =
      (ReferenceMeasure.measure (α := α)).map (fun a => (a, u0)) := by
    change
      (ReferenceMeasure.measure (α := α)).prod
        (ReferenceMeasure.measure (α := Fin 0 → 𝒮)) = _
    rw [hμ0, Measure.prod_dirac]
  let e := (X, Z)
  have hfun : (e : Ω → α × (Fin 0 → 𝒮)) = (fun a => (a, u0)) ∘ X := by
    funext ω
    exact Prod.ext rfl (hZω ω)
  have hmap : π.map e = (π.map X).map (fun a => (a, u0)) := by
    rw [hfun]
    exact (AEMeasurable.map_map_of_aemeasurable
      measurable_prodMk_right.aemeasurable hX.aemeasurable).symm
  have hfemb : MeasurableEmbedding (fun a : α => (a, u0)) := by
    refine
      ⟨fun _ _ h => congrArg Prod.fst h, measurable_prodMk_right, ?_⟩
    intro s hs
    have himg :
      (fun a : α => (a, u0)) '' s =
        s ×ˢ (Set.univ : Set (Fin 0 → 𝒮)) := by
      ext ⟨a, z⟩
      have hz : z = u0 := Subsingleton.elim z u0
      simp [Set.mem_prod, hz]
    rw [himg]
    exact hs.prod MeasurableSet.univ
  have habsX : π.map X ≪ ReferenceMeasure.measure (α := α) := by
    obtain ⟨ρ, _, hlaw⟩ := hX.exists_distribution
    rw [hlaw]
    exact withDensity_absolutelyContinuous _ _
  have hrd :=
    hfemb.rnDeriv_map (π.map X) (ReferenceMeasure.measure (α := α))
  have hrd' :
    (fun a => (π.map e).rnDeriv ReferenceMeasure.measure (a, u0)) =ᵐ[ReferenceMeasure.measure (α := α)]
    fun a => (π.map X).rnDeriv ReferenceMeasure.measure a := by
    simpa [hmap, href] using hrd
  have hnum :
    (fun ω => (π.map e).rnDeriv ReferenceMeasure.measure (e ω)) =ᵐ[π]
      fun ω => (π.map X).rnDeriv ReferenceMeasure.measure (X ω) := by
    have h1 := ae_of_ae_map hX.aemeasurable (habsX.ae_le hrd')
    filter_upwards [h1] with ω h
    rwa [congr_fun hfun ω]
  have hZmap : π.map Z = Measure.dirac u0 := by
    rw [hZ, Measure.map_const, measure_univ, one_smul]
  have habsZ : π.map Z ≪ ReferenceMeasure.measure (α := Fin 0 → 𝒮) := by
    rw [hZmap, hμ0]
  have hden :
    (fun ω => (π.map Z).rnDeriv ReferenceMeasure.measure (Z ω)) =ᵐ[π]
      fun _ => 1 := by
    have hself :
      (fun z => (π.map Z).rnDeriv ReferenceMeasure.measure z) =ᵐ[ReferenceMeasure.measure (α := Fin 0 → 𝒮)] 1 := by
      rw [hZmap, hμ0]
      exact Measure.rnDeriv_self _
    exact ae_of_ae_map (hZ ▸ measurable_const.aemeasurable) (habsZ.ae_le hself)
  filter_upwards [hnum, hden] with ω h hd
  change π.condProb e (e ω) = π.prob X (X ω)
  simp [Measure.condProb, Measure.prob]
  have hsnd : (fun ω' => (e ω').2) = Z := rfl
  have hval : (e ω).2 = Z ω := rfl
  rw [hsnd, hval, hd, h, div_eq_mul_inv, inv_one, mul_one]

/--
Appending a constant dummy coordinate to the conditioner does not change a
conditional random-argument density, almost surely.
-/
private lemma ProbCond_pair_elim0
  [MeasurableSpace Ω]
  [ReferenceMeasure 𝒮]
  [ReferenceMeasure α]
  [ReferenceMeasure β]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {X : Ω → α} {Y : Ω → β}
  {Z : Ω → Fin 0 → 𝒮}
-- given
  (hXY : SinglePSpace π (X, Y))
  (hZ : Z = fun _ => Fin.elim0)
  (hXYZ : SinglePSpace π (X, Y, Z)) :
-- imply
  ℙ[π](X | Y, Z) =ᵐ[π] ℙ[π](X | Y) := by
-- proof
  have hY : SinglePSpace π Y := SinglePSpace.of.SinglePSpace.snd hXY
  have hYZ : SinglePSpace π (Y, Z) := SinglePSpace_prod_elim0 hY hZ
  let u0 : Fin 0 → 𝒮 := Fin.elim0
  have hZω (ω : Ω) : Z ω = u0 := by rw [hZ]
  have hμ0 :
    ReferenceMeasure.measure (α := Fin 0 → 𝒮) = Measure.dirac u0 := by
    change Measure.pi (fun _ : Fin 0 => ReferenceMeasure.measure (α := 𝒮)) =
      Measure.dirac u0
    exact Measure.pi_of_empty _ u0
  have hrefY :
    ReferenceMeasure.measure (α := β × (Fin 0 → 𝒮)) =
      (ReferenceMeasure.measure (α := β)).map (fun y => (y, u0)) := by
    change
      (ReferenceMeasure.measure (α := β)).prod
        (ReferenceMeasure.measure (α := Fin 0 → 𝒮)) = _
    rw [hμ0, Measure.prod_dirac]
  have href :
    ReferenceMeasure.measure (α := α × (β × (Fin 0 → 𝒮))) =
      (ReferenceMeasure.measure (α := α × β)).map
        (Prod.map (id : α → α) (fun y : β => (y, u0))) := by
    change
      (ReferenceMeasure.measure (α := α)).prod
        ((ReferenceMeasure.measure (α := β)).prod
          (ReferenceMeasure.measure (α := Fin 0 → 𝒮))) = _
    rw [hμ0, Measure.prod_dirac]
    have hμprod :
      ReferenceMeasure.measure (α := α × β) =
        (ReferenceMeasure.measure (α := α)).prod
          (ReferenceMeasure.measure (α := β)) :=
      rfl
    rw [hμprod]
    simpa [Measure.map_id] using
      (Measure.map_prod_map
        (ReferenceMeasure.measure (α := α))
        (ReferenceMeasure.measure (α := β))
        measurable_id measurable_prodMk_right)
  have hfembY : MeasurableEmbedding (fun y : β => (y, u0)) := by
    refine ⟨fun _ _ h => congrArg Prod.fst h, measurable_prodMk_right, ?_⟩
    intro s hs
    have himg :
      (fun y : β => (y, u0)) '' s =
        s ×ˢ (Set.univ : Set (Fin 0 → 𝒮)) := by
      ext ⟨y, z⟩
      have hz : z = u0 := Subsingleton.elim z u0
      simp [Set.mem_prod, hz]
    rw [himg]
    exact hs.prod MeasurableSet.univ
  have hfemb :
    MeasurableEmbedding
      (Prod.map (id : α → α) (fun y : β => (y, u0))) :=
    MeasurableEmbedding.id.prodMap hfembY
  let e := (X, Y, Z)
  let f := (X, Y)
  let eYZ := (Y, Z)
  have hfun :
    (e : Ω → α × (β × (Fin 0 → 𝒮))) =
      Prod.map (id : α → α) (fun y : β => (y, u0)) ∘ (f : Ω → α × β) := by
    funext ω
    apply Prod.ext
    · rfl
    · exact Prod.ext rfl (hZω ω)
  have hfunY :
    (eYZ : Ω → β × (Fin 0 → 𝒮)) = (fun y => (y, u0)) ∘ Y := by
    funext ω
    exact Prod.ext rfl (hZω ω)
  have hmap :
    π.map e =
      (π.map f).map (Prod.map (id : α → α) (fun y : β => (y, u0))) := by
    rw [hfun]
    exact (AEMeasurable.map_map_of_aemeasurable
      hfemb.measurable.aemeasurable hXY.aemeasurable).symm
  have hmapY : π.map eYZ = (π.map Y).map (fun y => (y, u0)) := by
    rw [hfunY]
    exact (AEMeasurable.map_map_of_aemeasurable
      measurable_prodMk_right.aemeasurable hY.aemeasurable).symm
  have habsXY : π.map f ≪ ReferenceMeasure.measure (α := α × β) := by
    obtain ⟨ρ, _, hlaw⟩ := hXY.exists_distribution
    rw [hlaw]
    exact withDensity_absolutelyContinuous _ _
  have habsY : π.map Y ≪ ReferenceMeasure.measure (α := β) := by
    obtain ⟨ρ, _, hlaw⟩ := hY.exists_distribution
    rw [hlaw]
    exact withDensity_absolutelyContinuous _ _
  have hrd :=
    hfemb.rnDeriv_map (π.map f) (ReferenceMeasure.measure (α := α × β))
  have hrdY :=
    hfembY.rnDeriv_map (π.map Y) (ReferenceMeasure.measure (α := β))
  have hnum :
    (fun ω => (π.map e).rnDeriv ReferenceMeasure.measure (e ω)) =ᵐ[π]
      fun ω => (π.map f).rnDeriv ReferenceMeasure.measure (f ω) := by
    have hrd' :
      (fun p =>
        (π.map e).rnDeriv ReferenceMeasure.measure
          (Prod.map (id : α → α) (fun y : β => (y, u0)) p)) =ᵐ[ReferenceMeasure.measure (α := α × β)]
      fun p => (π.map f).rnDeriv ReferenceMeasure.measure p := by
      simpa [hmap, href] using hrd
    have h1 := ae_of_ae_map hXY.aemeasurable (habsXY.ae_le hrd')
    filter_upwards [h1] with ω h
    rwa [congr_fun hfun ω]
  have hden :
    (fun ω => (π.map eYZ).rnDeriv ReferenceMeasure.measure (eYZ ω)) =ᵐ[π]
      fun ω => (π.map Y).rnDeriv ReferenceMeasure.measure (Y ω) := by
    have hrd' :
      (fun y => (π.map eYZ).rnDeriv ReferenceMeasure.measure (y, u0)) =ᵐ[ReferenceMeasure.measure (α := β)]
      fun y => (π.map Y).rnDeriv ReferenceMeasure.measure y := by
      simpa [hmapY, hrefY] using hrdY
    have h1 := ae_of_ae_map hY.aemeasurable (habsY.ae_le hrd')
    filter_upwards [h1] with ω h
    rwa [congr_fun hfunY ω]
  filter_upwards [hnum, hden] with ω hn hd
  change π.condProb e (e ω) = π.condProb f (f ω)
  simp [Measure.condProb, Measure.prob]
  have hsnd_e : (fun ω' => (e ω').2) = eYZ := rfl
  have hsnd_f : (fun ω' => (f ω').2) = Y := rfl
  have hval_e : (e ω).2 = eYZ ω := rfl
  have hval_f : (f ω).2 = Y ω := rfl
  rw [hsnd_e, hsnd_f, hval_e, hval_f, hn, hd]

/--
Chain rule for a process prefix:

  \(\mathbb{P}_{\pi}(s[:n]) = \prod_{k<n} \mathbb{P}_{\pi}(s[k] \mid s[:k])\).

The identity holds almost surely with respect to \(\pi\), as a ratio of densities
against the product reference measure on prefixes. It is the special case of
[the conditional chain rule](?module=Random.Prob_Cond.ae.Prod_Prob_Cond_Joint.of.Measurable.All_Measurable)
with a deterministic auxiliary variable.
-/
@[path]
private lemma main
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
  have : ∀ k, SinglePSpace π (s[k], s[:k]) :=
    All_SinglePSpaceJointGet__GetSlice.of.All_SinglePSpaceGetSlice hP
  ℙ[π](s[:n]) =ᵐ[π] ∏ k ∈ Finset.range n, ℙ[π](s[k] | s[:k]) := by
-- proof
  have hPstep : ∀ k, SinglePSpace π (s[k], s[:k]) :=
    All_SinglePSpaceJointGet__GetSlice.of.All_SinglePSpaceGetSlice hP
  let Z : Ω → Fin 0 → 𝒮 := fun _ => Fin.elim0
  have hZ : Measurable Z := measurable_const
  have hZeq : Z = fun _ => Fin.elim0 := rfl
  have hPZ' :
    ∀ k : ℕ, SinglePSpace π (fun ω => (s[:k] : Ω → Fin k → 𝒮) ω, Z) :=
    fun k => SinglePSpace_prod_elim0 (hP k) hZeq
  have hPstep' :
    ∀ k : ℕ,
      SinglePSpace π
        (s[k], fun ω => (s[:k] : Ω → Fin k → 𝒮) ω, Z) :=
    fun k =>
      PSpace_Joint_Joint.of.PSpace_JointJoint
        (SinglePSpace_prod_elim0 (hPstep k) hZeq)
  have hutil :
    ℙ[π](s[:n] | Z) =ᵐ[π]
      ∏ k ∈ Finset.range n, ℙ[π](s[k] | s[:k], Z) :=
    @Prob_Cond.ae.Prod_Prob_Cond_Joint.of.Measurable.All_Measurable
      Ω 𝒮 (Fin 0 → 𝒮) _ _ ReferenceMeasure.piFin π _ s Z hs hZ hPZ' hPstep' n
  have hleft : ℙ[π](s[:n] | Z) =ᵐ[π] ℙ[π](s[:n]) :=
    ProbCond_elim0 (hP n) hZeq (hPZ' n)
  have hstep (k : ℕ) :
    ℙ[π](s[k] | s[:k], Z) =ᵐ[π] ℙ[π](s[k] | s[:k]) :=
    ProbCond_pair_elim0 (hPstep k) hZeq (hPstep' k)
  have hprod (n : ℕ) :
    (∏ k ∈ Finset.range n, ℙ[π](s[k] | s[:k], Z)) =ᵐ[π]
      (∏ k ∈ Finset.range n, ℙ[π](s[k] | s[:k])) := by
    induction n with
    | zero =>
      simp
    | succ m ih =>
      filter_upwards [ih, hstep m] with ω h₁ h₂
      simp only [Finset.prod_range_succ, Pi.mul_apply] at h₁ h₂ ⊢
      rw [h₁, h₂]
  filter_upwards [hutil, hleft, hprod n] with ω h₁ h₂ h₃
  exact h₂.symm.trans (h₁.trans h₃)


-- created on 2023-04-08
-- updated on 2026-11-18
