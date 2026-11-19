import Lemma.Random.All_MeasurableGet.is.All_MeasurableGetSlice
import Syntax.Probability.Probability
import Notation.Fun
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.MeasurableSpace.Prod
import Mathlib.MeasureTheory.Measure.Prod
open MeasureTheory ProbabilityTheory Random Fun


/--
Peeling the last coordinate off the prefix joint with an auxiliary variable:
`SinglePSpace` of `(s[:k + 1], Z)` transfers to `(s[k], s[:k], Z)`.
-/
private lemma SinglePSpace_Get_GetSlice_prod
  [MeasurableSpace Ω]
  [ReferenceMeasure 𝒮] [ReferenceMeasure 𝒵]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {s : ℕ ⇀ Ω → 𝒮} {Z : Ω → 𝒵}
-- given
  (hPZ : ∀ k : ℕ, SinglePSpace π (s[:k], Z))
  (k : ℕ) :
-- imply
  SinglePSpace π (s[k], (((s[:k] : Ω → Fin k → 𝒮), Z) : Ω → (Fin k → 𝒮) × 𝒵)) := by
-- proof
  let e :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin k.succ => 𝒮) (Fin.last k)
  let φ : (Fin k.succ → 𝒮) × 𝒵 ≃ᵐ 𝒮 × ((Fin k → 𝒮) × 𝒵) :=
    (MeasurableEquiv.prodCongr e (MeasurableEquiv.refl 𝒵)).trans
      MeasurableEquiv.prodAssoc
  let E : Ω → (Fin k.succ → 𝒮) × 𝒵 :=
    fun ω => ((s[:k.succ] : Ω → Fin k.succ → 𝒮) ω, Z ω)
  have hφ_apply (p : (Fin k.succ → 𝒮) × 𝒵) :
    φ p = ((e p.1).1, (e p.1).2, p.2) := rfl
  have hsplit (ω : Ω) :
    e ((s[:k.succ] : Ω → Fin k.succ → 𝒮) ω) =
      (s[k] ω, (s[:k] : Ω → Fin k → 𝒮) ω) := by
    refine Prod.ext ?_ ?_
    · simp [e, MeasurableEquiv.piFinSuccAbove_apply, Fun.getSlice, Function.getSlice,
        FunSlice.slice, Int.toNat_zero, Fin.last]
    ·
      funext j
      simp only [e, MeasurableEquiv.piFinSuccAbove_apply, Fun.getSlice,
        Function.getSlice, FunSlice.slice, Int.toNat_zero]
      refine congrArg (fun i : ℕ => s[i] ω) ?_
      rw [Fin.succAbove_last_apply, Fin.val_castSucc]
  have hcomp :
    (φ ∘ E) = fun ω => (s[k] ω, (s[:k] : Ω → Fin k → 𝒮) ω, Z ω) := by
    funext ω
    change φ (((s[:k.succ] : Ω → Fin k.succ → 𝒮) ω), Z ω) =
      (s[k] ω, (s[:k] : Ω → Fin k → 𝒮) ω, Z ω)
    rw [hφ_apply, hsplit]
  have he :
    MeasurePreserving e
      (ReferenceMeasure.measure (α := Fin k.succ → 𝒮))
      (ReferenceMeasure.measure (α := 𝒮 × (Fin k → 𝒮))) := by
    change MeasurePreserving e
      (Measure.pi fun _ : Fin k.succ => ReferenceMeasure.measure (α := 𝒮))
      ((ReferenceMeasure.measure (α := 𝒮)).prod
        (Measure.pi fun _ : Fin k => ReferenceMeasure.measure (α := 𝒮)))
    exact measurePreserving_piFinSuccAbove
      (fun _ : Fin k.succ => ReferenceMeasure.measure (α := 𝒮)) (Fin.last k)
  have hpres_map :
    MeasurePreserving (Prod.map e (id : 𝒵 → 𝒵))
      (ReferenceMeasure.measure (α := (Fin k.succ → 𝒮) × 𝒵))
      (((ReferenceMeasure.measure (α := 𝒮)).prod
          (ReferenceMeasure.measure (α := Fin k → 𝒮))).prod
        (ReferenceMeasure.measure (α := 𝒵))) :=
    he.prod (MeasurePreserving.id (μ := ReferenceMeasure.measure (α := 𝒵)))
  have hpres_assoc :
    MeasurePreserving MeasurableEquiv.prodAssoc
      (((ReferenceMeasure.measure (α := 𝒮)).prod
          (ReferenceMeasure.measure (α := Fin k → 𝒮))).prod
        (ReferenceMeasure.measure (α := 𝒵)))
      ((ReferenceMeasure.measure (α := 𝒮)).prod
        ((ReferenceMeasure.measure (α := Fin k → 𝒮)).prod
          (ReferenceMeasure.measure (α := 𝒵)))) :=
    ⟨MeasurableEquiv.prodAssoc.measurable, Measure.prodAssoc_prod⟩
  have hpres :
    MeasurePreserving φ
      (ReferenceMeasure.measure (α := (Fin k.succ → 𝒮) × 𝒵))
      (ReferenceMeasure.measure (α := 𝒮 × ((Fin k → 𝒮) × 𝒵))) := by
    have h := hpres_assoc.comp hpres_map
    convert h
    funext x
    rfl
  obtain ⟨ρ, hρm, hlaw⟩ := (hPZ k.succ).exists_distribution
  have hlaw' :
    π.map E =
      (ReferenceMeasure.measure
        (α := (Fin k.succ → 𝒮) × 𝒵)).withDensity ρ := by
    exact hlaw
  let ρ' : 𝒮 × ((Fin k → 𝒮) × 𝒵) → ENNReal := ρ ∘ φ.symm
  have hρ'm : Measurable ρ' := hρm.comp φ.symm.measurable
  have hE_ae : AEMeasurable E π := by
    exact (hPZ k.succ).aemeasurable
  have hmapE : π.map (φ ∘ E) = (π.map E).map φ :=
    (AEMeasurable.map_map_of_aemeasurable φ.measurable.aemeasurable hE_ae).symm
  have hwd :
    ((ReferenceMeasure.measure
        (α := (Fin k.succ → 𝒮) × 𝒵)).withDensity ρ).map φ =
      (ReferenceMeasure.measure (α := 𝒮 × ((Fin k → 𝒮) × 𝒵))).withDensity ρ' := by
    ext t ht
    rw [Measure.map_apply φ.measurable ht,
      withDensity_apply _ (φ.measurable ht),
      withDensity_apply _ ht, ← hpres.map_eq,
      setLIntegral_map ht hρ'm φ.measurable]
    refine setLIntegral_congr_fun (φ.measurable ht) ?_
    intro x _
    change ρ x = ρ (φ.symm (φ x))
    rw [φ.symm_apply_apply]
  refine {
    toIsProbabilityMeasure := inferInstance
    aemeasurable := ?_
    exists_distribution := ⟨ρ', hρ'm, ?_⟩
  }
  ·
    change AEMeasurable
      (fun ω => (s[k] ω, (s[:k] : Ω → Fin k → 𝒮) ω, Z ω)) π
    rw [← hcomp]
    exact φ.measurable.comp_aemeasurable hE_ae
  ·
    change π.map (fun ω => (s[k] ω, (s[:k] : Ω → Fin k → 𝒮) ω, Z ω)) =
      (ReferenceMeasure.measure (α := 𝒮 × ((Fin k → 𝒮) × 𝒵))).withDensity ρ'
    rw [← hcomp, hmapE, hlaw', hwd]

/--
Chain rule for a process prefix, conditioned on an auxiliary random variable \(Z\).
It holds almost surely with respect to \(\pi\), as a ratio of densities against the
reference measures of the state spaces:

  \(\mathbb{P}_{\pi}(s[:n] \mid Z) = \prod_{k<n} \mathbb{P}_{\pi}(s[k] \mid s[:k], Z)\).

The empty product (\(n = 0\)) is \(1\) off a \(\pi\)-null set where the density of \(Z\)
vanishes. Prefixes are taken with respect to the product reference measure on
\(\mathrm{Fin}\, n \to \mathcal{S}\).

| attributes | lemma |
| :---: | :---: |
| path | Random.Prob_Cond.ae.Prod_Prob_Cond_Joint.of.Measurable.All_Measurable |
| comm | Random.Prod_Prob_Cond_Joint.ae.Prob_Cond.of.Measurable.All_Measurable |
-/
@[path, comm]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure 𝒮] [ReferenceMeasure 𝒵]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {s : ℕ ⇀ Ω → 𝒮} {Z : Ω → 𝒵}
-- given
  (hs : ∀ k : ℕ, Measurable s[k])
  (hZ : Measurable Z)
  (hPZ : ∀ k : ℕ, SinglePSpace π (s[:k], Z))
  (n : ℕ) :
-- imply
  have : ∀ k : ℕ, Measurable s[:k] :=
    All_MeasurableGetSlice.of.All_MeasurableGet hs
  have :
    ∀ k : ℕ, SinglePSpace π (s[k], fun ω => (s[:k] : Ω → Fin k → 𝒮) ω, Z) :=
    SinglePSpace_Get_GetSlice_prod hPZ
  ℙ[π](s[:n] | Z) =ᵐ[π]
    ∏ k ∈ Finset.range n, ℙ[π](s[k] | s[:k], Z) := by
-- proof
  intro _ hPstep
  have hslice : ∀ k : ℕ, Measurable s[:k] :=
    All_MeasurableGetSlice.of.All_MeasurableGet hs
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.prod_empty]
    have := hPZ 0
    have ⟨_, _, hρ⟩ := (hPZ 0).exists_distribution
    let u0 : Fin 0 → 𝒮 := Fin.elim0
    have hss : Subsingleton (Fin 0 → 𝒮) := inferInstance
    have hconst (ω : Ω) : (s[:(0 : ℕ)] : Ω → Fin 0 → 𝒮) ω = u0 :=
      @Subsingleton.elim (Fin 0 → 𝒮) hss _ _
    have hμ0 :
      ReferenceMeasure.measure (α := Fin 0 → 𝒮) = Measure.dirac u0 := by
      change Measure.pi (fun _ : Fin 0 => ReferenceMeasure.measure (α := 𝒮)) =
        Measure.dirac u0
      exact Measure.pi_of_empty _ u0
    have href :
      ReferenceMeasure.measure (α := (Fin 0 → 𝒮) × 𝒵) =
        (ReferenceMeasure.measure (α := 𝒵)).map (Prod.mk u0) := by
      change
        (ReferenceMeasure.measure (α := Fin 0 → 𝒮)).prod
          (ReferenceMeasure.measure (α := 𝒵)) =
        _
      rw [hμ0, Measure.dirac_prod]
    let e := (fun ω => (s[:(0 : ℕ)] : Ω → Fin 0 → 𝒮) ω, Z)
    have he_eq : (e : Ω → (Fin 0 → 𝒮) × 𝒵) = fun ω => (u0, Z ω) := by
      funext ω
      apply Prod.ext
      · exact hconst ω
      · rfl
    have hmap_e : π.map e = (π.map Z).map (Prod.mk u0) := by
      rw [he_eq, Measure.map_map measurable_prodMk_left hZ]
      rfl
    have habs_e : π.map e ≪ ReferenceMeasure.measure (α := (Fin 0 → 𝒮) × 𝒵) := by
      rw [hρ]
      exact withDensity_absolutelyContinuous _ _
    have hfemb :
      MeasurableEmbedding (Prod.mk u0 : 𝒵 → (Fin 0 → 𝒮) × 𝒵) :=
      measurableEmbedding_prodMk_left u0
    have habsZ : π.map Z ≪ ReferenceMeasure.measure (α := 𝒵) := by
      intro t ht0
      obtain ⟨u, htu, hu, hu0⟩ := exists_measurable_superset_of_null ht0
      have himg : MeasurableSet (Prod.mk u0 '' u) :=
        hfemb.measurableSet_image.mpr hu
      have hpre : Prod.mk u0 ⁻¹' (Prod.mk u0 '' u) = u :=
        Function.Injective.preimage_image hfemb.injective u
      have : π.map e (Prod.mk u0 '' u) = 0 := by
        apply habs_e
        rwa [href, Measure.map_apply measurable_prodMk_left himg, hpre]
      have : π.map Z u = 0 := by
        rwa [hmap_e, Measure.map_apply measurable_prodMk_left himg, hpre] at this
      exact measure_mono_null htu this
    have hrd :=
      hfemb.rnDeriv_map (π.map Z) (ReferenceMeasure.measure (α := 𝒵))
    have hrd_Z :
      (fun z =>
        (π.map e).rnDeriv ReferenceMeasure.measure (u0, z)) =ᵐ[ReferenceMeasure.measure (α := 𝒵)]
        fun z =>
          (π.map Z).rnDeriv ReferenceMeasure.measure z := by
      simpa [hmap_e, href] using hrd
    have hcomp :
      (fun ω => (π.map e).rnDeriv ReferenceMeasure.measure (e ω)) =ᵐ[π]
        fun ω => (π.map Z).rnDeriv ReferenceMeasure.measure (Z ω) := by
      have h1 := ae_of_ae_map hZ.aemeasurable (habsZ.ae_le hrd_Z)
      filter_upwards [h1] with ω h
      rwa [congr_fun he_eq ω]
    have hpos :=
      ae_of_ae_map hZ.aemeasurable (Measure.rnDeriv_pos habsZ)
    have htop :=
      ae_of_ae_map hZ.aemeasurable
        (habsZ.ae_le ((π.map Z).rnDeriv_lt_top ReferenceMeasure.measure))
    filter_upwards [hcomp, hpos, htop] with ω heq hpos' htop'
    change π.condProb e (e ω) = 1
    simp [Measure.condProb, Measure.prob]
    have hsnd_fun : (fun ω' => (e ω').2) = Z := rfl
    have hsnd_val : (e ω).2 = Z ω := rfl
    rw [hsnd_fun, hsnd_val, heq]
    exact ENNReal.div_self hpos'.ne' htop'.ne
  | succ n ih =>
    let n1 : ℕ := n + 1
    have := hPZ n
    have := hPZ n1
    have := hPstep n
    have ⟨_, _, hρN⟩ := (hPZ n).exists_distribution
    have ⟨_, _, hρSucc⟩ := (hPZ n1).exists_distribution
    have ⟨_, _, hρf⟩ := (hPstep n).exists_distribution
    let eN := (fun ω => (s[:n] : Ω → Fin n → 𝒮) ω, Z)
    let eSucc := (fun ω => (s[:n1] : Ω → Fin (n + 1) → 𝒮) ω, Z)
    let f := (s[n], fun ω => (s[:n] : Ω → Fin n → 𝒮) ω, Z)
    have hsplit (ω : Ω) :
      MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => 𝒮) (Fin.last n)
        ((s[:n1] : Ω → Fin (n + 1) → 𝒮) ω) =
        (s[n] ω, (s[:n] : Ω → Fin n → 𝒮) ω) := by
      refine Prod.ext ?_ ?_
      · simp [MeasurableEquiv.piFinSuccAbove_apply, Fun.getSlice, Function.getSlice,
          FunSlice.slice, Int.toNat_zero, Fin.last]
      ·
        funext j
        simp only [MeasurableEquiv.piFinSuccAbove_apply, Fun.getSlice, Function.getSlice,
          FunSlice.slice, Int.toNat_zero]
        refine congrArg (fun i : ℕ => s[i] ω) ?_
        rw [Fin.succAbove_last_apply, Fin.val_castSucc]
    let φ :
      (Fin (n + 1) → 𝒮) × 𝒵 ≃ᵐ 𝒮 × ((Fin n → 𝒮) × 𝒵) :=
      (MeasurableEquiv.prodCongr
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => 𝒮) (Fin.last n))
        (MeasurableEquiv.refl 𝒵)).trans
      MeasurableEquiv.prodAssoc
    have hφ_apply (p : (Fin (n + 1) → 𝒮) × 𝒵) :
      φ p =
        ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => 𝒮) (Fin.last n) p.1).1,
          (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => 𝒮) (Fin.last n) p.1).2,
          p.2) :=
      rfl
    have hφ (ω : Ω) : φ (eSucc ω) = f ω := by
      rw [hφ_apply]
      have h1 : ((eSucc : Ω → (Fin (n + 1) → 𝒮) × 𝒵) ω).1 =
          (s[:n1] : Ω → Fin (n + 1) → 𝒮) ω := rfl
      have h2 : ((eSucc : Ω → (Fin (n + 1) → 𝒮) × 𝒵) ω).2 = Z ω := rfl
      rw [h1, h2, hsplit ω]
      rfl
    have hpres_split :
      MeasurePreserving
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => 𝒮) (Fin.last n))
        (ReferenceMeasure.measure (α := Fin (n + 1) → 𝒮))
        ((ReferenceMeasure.measure (α := 𝒮)).prod
          (ReferenceMeasure.measure (α := Fin n → 𝒮))) := by
      have hμs :
        ReferenceMeasure.measure (α := Fin (n + 1) → 𝒮) =
          Measure.pi fun _ : Fin (n + 1) => ReferenceMeasure.measure (α := 𝒮) := rfl
      have hμn :
        ReferenceMeasure.measure (α := Fin n → 𝒮) =
          Measure.pi fun _ : Fin n => ReferenceMeasure.measure (α := 𝒮) := rfl
      rw [hμs, hμn]
      apply measurePreserving_piFinSuccAbove
        (fun _ : Fin (n + 1) => ReferenceMeasure.measure (α := 𝒮)) (Fin.last n)
    have hpres_map :
      MeasurePreserving
        (Prod.map
          (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => 𝒮) (Fin.last n))
          (id : 𝒵 → 𝒵))
        (ReferenceMeasure.measure (α := (Fin (n + 1) → 𝒮) × 𝒵))
        (((ReferenceMeasure.measure (α := 𝒮)).prod
            (ReferenceMeasure.measure (α := Fin n → 𝒮))).prod
          (ReferenceMeasure.measure (α := 𝒵))) :=
      hpres_split.prod
        (MeasurePreserving.id (μ := ReferenceMeasure.measure (α := 𝒵)))
    have hpres_assoc :
      MeasurePreserving MeasurableEquiv.prodAssoc
        (((ReferenceMeasure.measure (α := 𝒮)).prod
            (ReferenceMeasure.measure (α := Fin n → 𝒮))).prod
          (ReferenceMeasure.measure (α := 𝒵)))
        ((ReferenceMeasure.measure (α := 𝒮)).prod
          ((ReferenceMeasure.measure (α := Fin n → 𝒮)).prod
            (ReferenceMeasure.measure (α := 𝒵)))) :=
      ⟨MeasurableEquiv.prodAssoc.measurable, Measure.prodAssoc_prod⟩
    have hpres :
      MeasurePreserving φ
        (ReferenceMeasure.measure (α := (Fin (n + 1) → 𝒮) × 𝒵))
        (ReferenceMeasure.measure (α := 𝒮 × ((Fin n → 𝒮) × 𝒵))) := by
      have hcomp := hpres_assoc.comp hpres_map
      convert hcomp
      funext x
      rfl
    have habs_succ :
      π.map eSucc ≪ ReferenceMeasure.measure (α := (Fin (n + 1) → 𝒮) × 𝒵) := by
      rw [hρSucc]
      exact withDensity_absolutelyContinuous _ _
    have habs_N :
      π.map eN ≪ ReferenceMeasure.measure (α := (Fin n → 𝒮) × 𝒵) := by
      rw [hρN]
      exact withDensity_absolutelyContinuous _ _
    have habs_f :
      π.map f ≪ ReferenceMeasure.measure (α := 𝒮 × ((Fin n → 𝒮) × 𝒵)) := by
      rw [hρf]
      exact withDensity_absolutelyContinuous _ _
    have hmap_φ : (π.map eSucc).map φ = π.map f := by
      have hfun :
        φ ∘ (eSucc : Ω → (Fin (n + 1) → 𝒮) × 𝒵) =
          (f : Ω → 𝒮 × ((Fin n → 𝒮) × 𝒵)) :=
        funext hφ
      have he_m : Measurable (eSucc : Ω → (Fin (n + 1) → 𝒮) × 𝒵) :=
        (hslice n1).prodMk hZ
      rw [Measure.map_map φ.measurable he_m, hfun]
    have href_φ :
      (ReferenceMeasure.measure (α := (Fin (n + 1) → 𝒮) × 𝒵)).map φ =
        ReferenceMeasure.measure (α := 𝒮 × ((Fin n → 𝒮) × 𝒵)) :=
      hpres.map_eq
    have hrd :=
      φ.measurableEmbedding.rnDeriv_map (π.map eSucc)
        (ReferenceMeasure.measure (α := (Fin (n + 1) → 𝒮) × 𝒵))
    let μsucc :=
      ReferenceMeasure.measure (α := (Fin (n + 1) → 𝒮) × 𝒵)
    have hrd' :
      (fun x => (π.map f).rnDeriv ReferenceMeasure.measure (φ x)) =ᵐ[μsucc]
        fun x => (π.map eSucc).rnDeriv ReferenceMeasure.measure x := by
      simpa [hmap_φ, href_φ] using hrd
    have hkey :
      (fun ω => (π.map eSucc).rnDeriv ReferenceMeasure.measure (eSucc ω)) =ᵐ[π]
        fun ω => (π.map f).rnDeriv ReferenceMeasure.measure (f ω) := by
      have h1 :=
        ae_of_ae_map (hslice n1 |>.prodMk hZ).aemeasurable (habs_succ.ae_le hrd')
      filter_upwards [h1] with ω h
      exact
        (h.symm.trans
          (congrArg (fun x => (π.map f).rnDeriv ReferenceMeasure.measure x) (hφ ω)))
    have hposN :=
      ae_of_ae_map (hslice n |>.prodMk hZ).aemeasurable (Measure.rnDeriv_pos habs_N)
    have htopN :=
      ae_of_ae_map (hslice n |>.prodMk hZ).aemeasurable
        (habs_N.ae_le ((π.map eN).rnDeriv_lt_top ReferenceMeasure.measure))
    have hprod :
      ℙ[π](s[:n1] | Z) =ᵐ[π]
        ℙ[π](s[:n] | Z) * ℙ[π](s[n] | s[:n], Z) := by
      filter_upwards [hkey, hposN, htopN] with ω hkey' hpos' htop'
      change π.condProb eSucc (eSucc ω) =
        π.condProb eN (eN ω) * π.condProb f (f ω)
      simp [Measure.condProb, Measure.prob]
      have hsndSucc : (fun ω' => (eSucc ω').2) = Z := rfl
      have hsndN : (fun ω' => (eN ω').2) = Z := rfl
      have hsndF : (fun ω' => (f ω').2) = (eN : Ω → (Fin n → 𝒮) × 𝒵) := rfl
      have hvalSucc : (eSucc ω).2 = Z ω := rfl
      have hvalN : (eN ω).2 = Z ω := rfl
      have hvalF : (f ω).2 = eN ω := rfl
      rw [hsndSucc, hsndN, hsndF, hvalSucc, hvalN, hvalF, hkey']
      set a := (π.map eN).rnDeriv ReferenceMeasure.measure (eN ω)
      set b := (π.map f).rnDeriv ReferenceMeasure.measure (f ω)
      set c := (π.map Z).rnDeriv ReferenceMeasure.measure (Z ω)
      -- b / c = (a / c) * (b / a)
      rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
      calc
        _ = 1 * (b * c⁻¹) :=
          (one_mul (b * c⁻¹)).symm
        _ = a * a⁻¹ * (b * c⁻¹) :=
          congrArg (fun x => x * (b * c⁻¹))
            (ENNReal.mul_inv_cancel hpos'.ne' htop'.ne).symm
        _ = b * c⁻¹ * (a * a⁻¹) :=
          mul_comm (a * a⁻¹) (b * c⁻¹)
        _ = b * c⁻¹ * a * a⁻¹ :=
          (mul_assoc (b * c⁻¹) a a⁻¹).symm
        _ = a * (b * c⁻¹) * a⁻¹ :=
          congrArg (fun x => x * a⁻¹) (mul_comm (b * c⁻¹) a)
        _ = a * (b * c⁻¹ * a⁻¹) :=
          mul_assoc a (b * c⁻¹) a⁻¹
        _ = a * (c⁻¹ * b * a⁻¹) :=
          congrArg (fun x => a * (x * a⁻¹)) (mul_comm b c⁻¹)
        _ = a * (c⁻¹ * (b * a⁻¹)) :=
          congrArg (fun x => a * x) (mul_assoc c⁻¹ b a⁻¹)
        _ = a * c⁻¹ * (b * a⁻¹) :=
          (mul_assoc a c⁻¹ (b * a⁻¹)).symm
    filter_upwards [hprod, ih] with ω h₁ h₂
    rw [Finset.prod_range_succ]
    simp only [Pi.mul_apply] at h₁ h₂ ⊢
    rw [h₁, h₂]


-- created on 2023-10-13
-- updated on 2026-11-19
