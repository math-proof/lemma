import Lemma.Random.All_Eq_MulProbCond.of.PSpace_Joint
import Lemma.Random.PSpace_JointJoint.is.PSpace_Joint_Joint
import Lemma.Random.PSpace_Joint
open ProbabilityTheory MeasureTheory Random MeasurableSpace
open scoped ENNReal


@[main]
private lemma main
  [MeasurableSpace Ω] [StandardBorelSpace Ω]
  [ReferenceMeasure α] [StandardBorelSpace α] [Nonempty α]
  [ReferenceMeasure β] [StandardBorelSpace β] [Nonempty β]
  [ReferenceMeasure γ]
  {π : Measure Ω} [IsFiniteMeasure π]
  {x : Ω → α} {y : Ω → β} {z : Ω → γ}
-- given
  (hx : Measurable x) (hy : Measurable y) (hz : Measurable z)
  (hPxyz : PSpace π (x, y, z))
  (hCI : x ⟂ᵢ[π] y | z) :
-- imply
  have : PSpace π (y, z) := PSpace.of.PSpace_Joint.snd hPxyz
  have : PSpace π z := PSpace.of.PSpace_Joint.snd this
  have : PSpace π (x, z) := PSpace_Joint.comm
    (PSpace.of.PSpace_Joint.fst (PSpace_JointJoint.of.PSpace_Joint_Joint (PSpace_Joint.comm (PSpace_JointJoint.of.PSpace_Joint_Joint hPxyz))))
  ∀ᵐ «x.bvar» ∂ReferenceMeasure.measure,
    ∀ᵐ «y.bvar» ∂ReferenceMeasure.measure,
      ∀ᵐ «z.bvar» ∂ReferenceMeasure.measure,
        ℙ[π](y = «y.bvar» ∧ z = «z.bvar») ≠ 0 →
          ℙ[π](x = «x.bvar» | y = «y.bvar» ∧ z = «z.bvar») =
            ℙ[π](x = «x.bvar» | z = «z.bvar») := by
-- proof
  intro hPyz hPz hPxz
  let μ : Measure α := ReferenceMeasure.measure
  let ν : Measure β := ReferenceMeasure.measure
  let ξ : Measure γ := ReferenceMeasure.measure
  let κ := condDistrib x z π
  let η := condDistrib y z π
  let pz := π.prob z
  let pxz := π.prob (x, z)
  let pyz := π.prob (y, z)
  let pxyz := π.prob (x, (y, z))
  let ρ : Measure (α × β × γ) := μ.prod (ν.prod ξ)
  have hlaw_z : π.map z = ξ.withDensity pz := PSpace.map_eq_withDensity_density
  have hlaw_xz : π.map (x, z) = (μ.prod ξ).withDensity pxz :=
    PSpace.map_eq_withDensity_density
  have hlaw_yz : π.map (y, z) = (ν.prod ξ).withDensity pyz :=
    PSpace.map_eq_withDensity_density
  have hlaw_xyz : π.map (x, (y, z)) = ρ.withDensity pxyz :=
    PSpace.map_eq_withDensity_density
  have hκ_dis : π.map (fun ω ↦ (z ω, x ω)) = π.map z ⊗ₘ κ :=
    (compProd_map_condDistrib (Y := x) (X := z) (μ := π) hx.aemeasurable).symm
  have hη_dis : π.map (fun ω ↦ (z ω, y ω)) = π.map z ⊗ₘ η :=
    (compProd_map_condDistrib (Y := y) (X := z) (μ := π) hy.aemeasurable).symm
  have h_xz_ac : π.map (x, z) ≪ μ.prod ξ := by
    rw [hlaw_xz]; exact withDensity_absolutelyContinuous _ _
  have h_yz_ac : π.map (y, z) ≪ ν.prod ξ := by
    rw [hlaw_yz]; exact withDensity_absolutelyContinuous _ _
  have h_zx :
      π.map (fun ω ↦ (z ω, x ω)) = (π.map (x, z)).map Prod.swap := by
    change π.map (fun ω ↦ (z ω, x ω)) =
      (π.map (fun ω ↦ (x ω, z ω))).map Prod.swap
    rw [Measure.map_map measurable_swap (hx.prodMk hz)]; rfl
  have h_zy :
      π.map (fun ω ↦ (z ω, y ω)) = (π.map (y, z)).map Prod.swap := by
    change π.map (fun ω ↦ (z ω, y ω)) =
      (π.map (fun ω ↦ (y ω, z ω))).map Prod.swap
    rw [Measure.map_map measurable_swap (hy.prodMk hz)]; rfl
  have h_zx_ac : π.map (fun ω ↦ (z ω, x ω)) ≪ ξ.prod μ := by
    have h := h_xz_ac.map (f := Prod.swap) measurable_swap
    simpa [← h_zx, Measure.prod_swap] using h
  have h_zy_ac : π.map (fun ω ↦ (z ω, y ω)) ≪ ξ.prod ν := by
    have h := h_yz_ac.map (f := Prod.swap) measurable_swap
    simpa [← h_zy, Measure.prod_swap] using h
  -- Fiber densitization via Fubini (avoids Kernel.const / IsFiniteMeasure on refs).
  have hpz : Measurable pz := Measure.measurable_rnDeriv _ _
  have hpxz : Measurable pxz := Measure.measurable_rnDeriv _ _
  have hpyz : Measurable pyz := Measure.measurable_rnDeriv _ _
  have hpxyz : Measurable pxyz := Measure.measurable_rnDeriv _ _
  have h_zx_dens :
      π.map (fun ω ↦ (z ω, x ω)) =
        (ξ.prod μ).withDensity (fun p : γ × α ↦ pxz (p.2, p.1)) := by
    rw [h_zx, hlaw_xz]
    ext s hs
    rw [Measure.map_apply measurable_swap hs, withDensity_apply _ (measurable_swap hs),
      withDensity_apply _ hs]
    have hμξ : μ.prod ξ = (ξ.prod μ).map Prod.swap := Measure.prod_swap.symm
    rw [hμξ, setLIntegral_map (measurable_swap hs) hpxz measurable_swap]
    refine setLIntegral_congr_fun hs fun q _ => ?_
    simp [Prod.swap]
  have h_zy_dens :
      π.map (fun ω ↦ (z ω, y ω)) =
        (ξ.prod ν).withDensity (fun p : γ × β ↦ pyz (p.2, p.1)) := by
    rw [h_zy, hlaw_yz]
    ext s hs
    rw [Measure.map_apply measurable_swap hs, withDensity_apply _ (measurable_swap hs),
      withDensity_apply _ hs]
    have hνξ : ν.prod ξ = (ξ.prod ν).map Prod.swap := Measure.prod_swap.symm
    rw [hνξ, setLIntegral_map (measurable_swap hs) hpyz measurable_swap]
    refine setLIntegral_congr_fun hs fun q _ => ?_
    simp [Prod.swap]
  -- Slice: ae c, κ c A * pz c = ∫_A pxz(a,c) ∂μ
  have hκ_slice (A : Set α) (hA : MeasurableSet A) :
      (fun c ↦ κ c A * pz c) =ᵐ[ξ] fun c ↦ ∫⁻ a in A, pxz (a, c) ∂μ := by
    have hκA : Measurable fun c ↦ κ c A := Kernel.measurable_coe κ hA
    refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite
      (hκA.mul hpz) (by fun_prop) fun C hC _ ↦ ?_
    have hL :
        ∫⁻ c in C, κ c A * pz c ∂ξ =
          π.map (fun ω ↦ (z ω, x ω)) (C ×ˢ A) := by
      have : π.map (fun ω ↦ (z ω, x ω)) (C ×ˢ A) = ∫⁻ c in C, κ c A ∂π.map z := by
        rw [hκ_dis, Measure.compProd_apply_prod hC hA]
      rw [this, hlaw_z,
        setLIntegral_withDensity_eq_setLIntegral_mul ξ hpz hκA hC]
      refine setLIntegral_congr_fun hC fun c _ => mul_comm _ _
    have hR :
        ∫⁻ c in C, ∫⁻ a in A, pxz (a, c) ∂μ ∂ξ =
          π.map (fun ω ↦ (z ω, x ω)) (C ×ˢ A) := by
      have hF :
          ∫⁻ c in C, ∫⁻ a in A, pxz (a, c) ∂μ ∂ξ =
            ∫⁻ p in C ×ˢ A, pxz (p.2, p.1) ∂(ξ.prod μ) := by
        rw [← setLIntegral_prod (μ := ξ) (ν := μ) (s := C) (t := A)
          (fun p : γ × α ↦ pxz (p.2, p.1))
          ((hpxz.comp measurable_swap).aemeasurable)]
      have : ∫⁻ p in C ×ˢ A, pxz (p.2, p.1) ∂(ξ.prod μ) =
          π.map (fun ω ↦ (z ω, x ω)) (C ×ˢ A) := by
        rw [h_zx_dens, withDensity_apply _ (hC.prod hA)]
      exact hF.trans this
    rw [hL, hR]
  have hη_slice (B : Set β) (hB : MeasurableSet B) :
      (fun c ↦ η c B * pz c) =ᵐ[ξ] fun c ↦ ∫⁻ b in B, pyz (b, c) ∂ν := by
    have hηB : Measurable fun c ↦ η c B := Kernel.measurable_coe η hB
    refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite
      (hηB.mul hpz) (by fun_prop) fun C hC _ ↦ ?_
    have hL :
        ∫⁻ c in C, η c B * pz c ∂ξ =
          π.map (fun ω ↦ (z ω, y ω)) (C ×ˢ B) := by
      have : π.map (fun ω ↦ (z ω, y ω)) (C ×ˢ B) = ∫⁻ c in C, η c B ∂π.map z := by
        rw [hη_dis, Measure.compProd_apply_prod hC hB]
      rw [this, hlaw_z,
        setLIntegral_withDensity_eq_setLIntegral_mul ξ hpz hηB hC]
      refine setLIntegral_congr_fun hC fun c _ => mul_comm _ _
    have hR :
        ∫⁻ c in C, ∫⁻ b in B, pyz (b, c) ∂ν ∂ξ =
          π.map (fun ω ↦ (z ω, y ω)) (C ×ˢ B) := by
      have hF :
          ∫⁻ c in C, ∫⁻ b in B, pyz (b, c) ∂ν ∂ξ =
            ∫⁻ p in C ×ˢ B, pyz (p.2, p.1) ∂(ξ.prod ν) := by
        rw [← setLIntegral_prod (μ := ξ) (ν := ν) (s := C) (t := B)
          (fun p : γ × β ↦ pyz (p.2, p.1))
          ((hpyz.comp measurable_swap).aemeasurable)]
      have : ∫⁻ p in C ×ˢ B, pyz (p.2, p.1) ∂(ξ.prod ν) =
          π.map (fun ω ↦ (z ω, y ω)) (C ×ˢ B) := by
        rw [h_zy_dens, withDensity_apply _ (hC.prod hB)]
      exact hF.trans this
    rw [hL, hR]
  have hCI_map :
      π.map (fun ω ↦ (z ω, x ω, y ω)) =
        (Kernel.id ×ₖ (κ ×ₖ η)) ∘ₘ π.map z :=
    (condIndepFun_iff_map_prod_eq_prod_condDistrib_prod_condDistrib hx hy hz).1 hCI
  have h_reorder :
      π.map (x, (y, z)) =
        (π.map (fun ω ↦ (z ω, x ω, y ω))).map
          (fun p : γ × α × β ↦ (p.2.1, (p.2.2, p.1))) := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]; rfl
  -- CondIndep rectangle mass
  have h_xyz_mass (A : Set α) (B : Set β) (C : Set γ)
      (hA : MeasurableSet A) (hB : MeasurableSet B) (hC : MeasurableSet C) :
      π.map (x, (y, z)) (A ×ˢ (B ×ˢ C)) =
        ∫⁻ c in C, κ c A * η c B * pz c ∂ξ := by
    have hpre :
        (fun p : γ × α × β ↦ (p.2.1, (p.2.2, p.1))) ⁻¹' (A ×ˢ (B ×ˢ C)) =
          C ×ˢ (A ×ˢ B) := by
      ext ⟨c, a, b⟩; constructor <;> simp_all [and_comm, and_assoc]
    have hLHS :
        π.map (x, (y, z)) (A ×ˢ (B ×ˢ C)) =
          π.map (fun ω ↦ (z ω, x ω, y ω)) (C ×ˢ (A ×ˢ B)) := by
      rw [h_reorder, Measure.map_apply (by fun_prop) (hA.prod (hB.prod hC)), hpre]
    have hκAηB : Measurable fun c ↦ κ c A * η c B :=
      (Kernel.measurable_coe κ hA).mul (Kernel.measurable_coe η hB)
    rw [hLHS, hCI_map, ← Measure.compProd_eq_comp_prod]
    have hprod :
        (π.map z ⊗ₘ (κ ×ₖ η)) (C ×ˢ (A ×ˢ B)) =
          ∫⁻ c in C, κ c A * η c B ∂π.map z := by
      rw [Measure.compProd_apply_prod hC (hA.prod hB)]
      refine setLIntegral_congr_fun hC fun c _ => Kernel.prod_apply_prod
    rw [hprod, hlaw_z,
      setLIntegral_withDensity_eq_setLIntegral_mul ξ hpz hκAηB hC]
    refine setLIntegral_congr_fun hC fun c _ => mul_comm (pz c) _
  have h_xyz_slice (A : Set α) (B : Set β) (hA : MeasurableSet A) (hB : MeasurableSet B) :
      (fun c ↦ ∫⁻ a in A, ∫⁻ b in B, pxyz (a, (b, c)) ∂ν ∂μ) =ᵐ[ξ]
        fun c ↦ κ c A * η c B * pz c := by
    have hmeasR : Measurable fun c ↦ κ c A * η c B * pz c :=
      ((Kernel.measurable_coe κ hA).mul (Kernel.measurable_coe η hB)).mul hpz
    refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite (by fun_prop) hmeasR
      fun C hC _ ↦ ?_
    have hL :
        ∫⁻ c in C, ∫⁻ a in A, ∫⁻ b in B, pxyz (a, (b, c)) ∂ν ∂μ ∂ξ =
          π.map (x, (y, z)) (A ×ˢ (B ×ˢ C)) := by
      have hF :
          ∫⁻ c in C, ∫⁻ a in A, ∫⁻ b in B, pxyz (a, (b, c)) ∂ν ∂μ ∂ξ =
            ∫⁻ q in A ×ˢ (B ×ˢ C), pxyz q ∂ρ := by
        have h1 :
            ∫⁻ q in A ×ˢ (B ×ˢ C), pxyz q ∂ρ =
              ∫⁻ bc in B ×ˢ C, ∫⁻ a in A, pxyz (a, bc) ∂μ ∂(ν.prod ξ) :=
          setLIntegral_prod_symm (μ := μ) (ν := ν.prod ξ) (s := A) (t := B ×ˢ C)
            pxyz hpxyz.aemeasurable
        have h2 :
            ∫⁻ bc in B ×ˢ C, ∫⁻ a in A, pxyz (a, bc) ∂μ ∂(ν.prod ξ) =
              ∫⁻ c in C, ∫⁻ b in B, ∫⁻ a in A, pxyz (a, (b, c)) ∂μ ∂ν ∂ξ := by
          rw [setLIntegral_prod_symm (μ := ν) (ν := ξ) (s := B) (t := C)
            (fun bc ↦ ∫⁻ a in A, pxyz (a, bc) ∂μ)
            (by
              refine Measurable.aemeasurable ?_
              exact Measurable.lintegral_prod_left' (by fun_prop))]
        have h3 :
            ∫⁻ c in C, ∫⁻ b in B, ∫⁻ a in A, pxyz (a, (b, c)) ∂μ ∂ν ∂ξ =
              ∫⁻ c in C, ∫⁻ a in A, ∫⁻ b in B, pxyz (a, (b, c)) ∂ν ∂μ ∂ξ := by
          refine setLIntegral_congr_fun hC fun c _ => ?_
          exact lintegral_lintegral_swap (by
            refine (hpxyz.comp ?_).aemeasurable
            -- (b,a) ↦ (a,(b,c))
            exact measurable_snd.prodMk (measurable_fst.prodMk measurable_const))
        exact (h1.trans h2 |>.trans h3).symm
      have : ∫⁻ q in A ×ˢ (B ×ˢ C), pxyz q ∂ρ =
          π.map (x, (y, z)) (A ×ˢ (B ×ˢ C)) := by
        rw [hlaw_xyz, withDensity_apply _ (hA.prod (hB.prod hC))]
      exact hF.trans this
    have hR :
        ∫⁻ c in C, κ c A * η c B * pz c ∂ξ =
          π.map (x, (y, z)) (A ×ˢ (B ×ˢ C)) :=
      (h_xyz_mass A B C hA hB hC).symm
    rw [hL, hR]
  -- Target densities
  let fL : α × β × γ → ENNReal := fun p ↦ pxyz (p.1, p.2) * pz p.2.2
  let fR : α × β × γ → ENNReal := fun p ↦ pxz (p.1, p.2.2) * pyz (p.2.1, p.2.2)
  have hfL : Measurable fL := hpxyz.mul (hpz.comp measurable_snd.snd)
  have hfR : Measurable fR :=
    (hpxz.comp (measurable_fst.prodMk measurable_snd.snd)).mul
      (hpyz.comp (measurable_snd.fst.prodMk measurable_snd.snd))
  -- Rectangles: ∫ fL = ∫ fR
  have h_rect (A : Set α) (B : Set β) (C : Set γ)
      (hA : MeasurableSet A) (hB : MeasurableSet B) (hC : MeasurableSet C) :
      ∫⁻ p in A ×ˢ (B ×ˢ C), fL p ∂ρ = ∫⁻ p in A ×ˢ (B ×ˢ C), fR p ∂ρ := by
    have hL :
        ∫⁻ p in A ×ˢ (B ×ˢ C), fL p ∂ρ =
          ∫⁻ c in C, pz c * (∫⁻ a in A, ∫⁻ b in B, pxyz (a, (b, c)) ∂ν ∂μ) ∂ξ := by
      have h1 :
          ∫⁻ p in A ×ˢ (B ×ˢ C), fL p ∂ρ =
            ∫⁻ c in C, ∫⁻ b in B, ∫⁻ a in A,
              pxyz (a, (b, c)) * pz c ∂μ ∂ν ∂ξ := by
        have hsymm1 :
            ∫⁻ p in A ×ˢ (B ×ˢ C), fL p ∂ρ =
              ∫⁻ bc in B ×ˢ C, ∫⁻ a in A, fL (a, bc) ∂μ ∂(ν.prod ξ) :=
          setLIntegral_prod_symm (μ := μ) (ν := ν.prod ξ) (s := A) (t := B ×ˢ C)
            fL hfL.aemeasurable
        have hsymm2 :
            ∫⁻ bc in B ×ˢ C, ∫⁻ a in A, fL (a, bc) ∂μ ∂(ν.prod ξ) =
              ∫⁻ c in C, ∫⁻ b in B, ∫⁻ a in A, fL (a, (b, c)) ∂μ ∂ν ∂ξ := by
          rw [setLIntegral_prod_symm (μ := ν) (ν := ξ) (s := B) (t := C)
            (fun bc ↦ ∫⁻ a in A, fL (a, bc) ∂μ)
            (by
              refine Measurable.aemeasurable ?_
              exact Measurable.lintegral_prod_left' (by fun_prop))]
        refine hsymm1.trans (hsymm2.trans ?_)
        refine setLIntegral_congr_fun hC fun c _ => ?_
        refine setLIntegral_congr_fun hB fun b _ => ?_
        refine setLIntegral_congr_fun hA fun a _ => rfl
      have h2 :
          ∫⁻ c in C, ∫⁻ b in B, ∫⁻ a in A, pxyz (a, (b, c)) * pz c ∂μ ∂ν ∂ξ =
            ∫⁻ c in C, ∫⁻ a in A, ∫⁻ b in B, pxyz (a, (b, c)) * pz c ∂ν ∂μ ∂ξ := by
        refine setLIntegral_congr_fun hC fun c _ => ?_
        exact lintegral_lintegral_swap (by
          refine (((hpxyz.comp ?_).mul measurable_const)).aemeasurable
          exact measurable_snd.prodMk (measurable_fst.prodMk measurable_const))
      have h3 :
          ∫⁻ c in C, ∫⁻ a in A, ∫⁻ b in B, pxyz (a, (b, c)) * pz c ∂ν ∂μ ∂ξ =
            ∫⁻ c in C, pz c * (∫⁻ a in A, ∫⁻ b in B, pxyz (a, (b, c)) ∂ν ∂μ) ∂ξ := by
        refine setLIntegral_congr_fun hC fun c _ => ?_
        have hmul :
            ∫⁻ a in A, ∫⁻ b in B, pxyz (a, (b, c)) * pz c ∂ν ∂μ =
              ∫⁻ a in A, ∫⁻ b in B, pz c * pxyz (a, (b, c)) ∂ν ∂μ := by
          refine setLIntegral_congr_fun hA fun a _ => ?_
          refine setLIntegral_congr_fun hB fun b _ => mul_comm _ _
        refine hmul.trans ?_
        have hmul1 :
            ∫⁻ a in A, ∫⁻ b in B, pz c * pxyz (a, (b, c)) ∂ν ∂μ =
              ∫⁻ a in A, pz c * (∫⁻ b in B, pxyz (a, (b, c)) ∂ν) ∂μ := by
          refine setLIntegral_congr_fun hA fun a _ => ?_
          exact lintegral_const_mul (pz c)
            (hpxyz.comp
              (measurable_const.prodMk (measurable_id.prodMk measurable_const)))
        refine hmul1.trans ?_
        exact lintegral_const_mul (pz c) (Measurable.lintegral_prod_right (by fun_prop))
      exact h1.trans (h2.trans h3)
    have hR :
        ∫⁻ p in A ×ˢ (B ×ˢ C), fR p ∂ρ =
          ∫⁻ c in C, (∫⁻ a in A, pxz (a, c) ∂μ) * (∫⁻ b in B, pyz (b, c) ∂ν) ∂ξ := by
      have h1 :
          ∫⁻ p in A ×ˢ (B ×ˢ C), fR p ∂ρ =
            ∫⁻ c in C, ∫⁻ b in B, ∫⁻ a in A,
              pxz (a, c) * pyz (b, c) ∂μ ∂ν ∂ξ := by
        have hsymm1 :
            ∫⁻ p in A ×ˢ (B ×ˢ C), fR p ∂ρ =
              ∫⁻ bc in B ×ˢ C, ∫⁻ a in A, fR (a, bc) ∂μ ∂(ν.prod ξ) :=
          setLIntegral_prod_symm (μ := μ) (ν := ν.prod ξ) (s := A) (t := B ×ˢ C)
            fR hfR.aemeasurable
        have hsymm2 :
            ∫⁻ bc in B ×ˢ C, ∫⁻ a in A, fR (a, bc) ∂μ ∂(ν.prod ξ) =
              ∫⁻ c in C, ∫⁻ b in B, ∫⁻ a in A, fR (a, (b, c)) ∂μ ∂ν ∂ξ := by
          rw [setLIntegral_prod_symm (μ := ν) (ν := ξ) (s := B) (t := C)
            (fun bc ↦ ∫⁻ a in A, fR (a, bc) ∂μ)
            (by
              refine Measurable.aemeasurable ?_
              exact Measurable.lintegral_prod_left' (by fun_prop))]
        refine hsymm1.trans (hsymm2.trans ?_)
        refine setLIntegral_congr_fun hC fun c _ => ?_
        refine setLIntegral_congr_fun hB fun b _ => ?_
        refine setLIntegral_congr_fun hA fun a _ => rfl
      have h2 :
          ∫⁻ c in C, ∫⁻ b in B, ∫⁻ a in A, pxz (a, c) * pyz (b, c) ∂μ ∂ν ∂ξ =
            ∫⁻ c in C, ∫⁻ a in A, ∫⁻ b in B, pxz (a, c) * pyz (b, c) ∂ν ∂μ ∂ξ := by
        refine setLIntegral_congr_fun hC fun c _ => ?_
        exact lintegral_lintegral_swap (by
          -- (b,a) ↦ pxz(a,c)*pyz(b,c)
          refine ((hpxz.comp (measurable_snd.prodMk measurable_const)).mul
            (hpyz.comp (measurable_fst.prodMk measurable_const))).aemeasurable)
      have h3 :
          ∫⁻ c in C, ∫⁻ a in A, ∫⁻ b in B, pxz (a, c) * pyz (b, c) ∂ν ∂μ ∂ξ =
            ∫⁻ c in C, (∫⁻ a in A, pxz (a, c) ∂μ) * (∫⁻ b in B, pyz (b, c) ∂ν) ∂ξ := by
        refine setLIntegral_congr_fun hC fun c _ => ?_
        have hsep' :
            ∫⁻ a in A, ∫⁻ b in B, pxz (a, c) * pyz (b, c) ∂ν ∂μ =
              ∫⁻ a in A, pxz (a, c) * (∫⁻ b in B, pyz (b, c) ∂ν) ∂μ := by
          refine setLIntegral_congr_fun hA fun a _ =>
            (lintegral_const_mul (pxz (a, c))
              (hpyz.comp measurable_prodMk_right))
        refine hsep'.trans ?_
        exact lintegral_mul_const (∫⁻ b in B, pyz (b, c) ∂ν)
          (hpxz.comp measurable_prodMk_right)
      exact h1.trans (h2.trans h3)
    have hL' :
        ∫⁻ p in A ×ˢ (B ×ˢ C), fL p ∂ρ =
          ∫⁻ c in C, pz c * (κ c A * η c B * pz c) ∂ξ := by
      rw [hL]
      refine setLIntegral_congr_fun_ae hC ?_
      filter_upwards [h_xyz_slice A B hA hB] with c hc _
      exact congrArg (fun t => pz c * t) hc
    have hR' :
        ∫⁻ p in A ×ˢ (B ×ˢ C), fR p ∂ρ =
          ∫⁻ c in C, (κ c A * pz c) * (η c B * pz c) ∂ξ := by
      rw [hR]
      refine setLIntegral_congr_fun_ae hC ?_
      filter_upwards [hκ_slice A hA, hη_slice B hB] with c hκ hη _
      rw [hκ, hη]
    rw [hL', hR']
    refine setLIntegral_congr_fun hC fun c _ => ?_
    simp only [mul_comm, mul_left_comm, mul_assoc]
  have hpz_lt : ∀ᵐ c ∂ξ, pz c < ∞ :=
    ae_lt_top hpz (by
      have : ∫⁻ c, pz c ∂ξ = 1 := by
        have h : (ξ.withDensity pz) Set.univ = ∫⁻ c, pz c ∂ξ := by
          rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
        have : IsProbabilityMeasure (π.map z) :=
          Measure.isProbabilityMeasure_map hPz.aemeasurable
        rw [← hlaw_z, measure_univ] at h
        exact h.symm
      rw [this]; norm_num)
  -- Path A: withDensity equality on rectangles → σ-finite π-system uniqueness
  have : SigmaFinite μ := inferInstance
  have : SigmaFinite ν := inferInstance
  have : SigmaFinite ξ := inferInstance
  have : SigmaFinite ρ := inferInstance
  have hpz_top_null : ξ {c | pz c = (∞ : ENNReal)} = 0 := by
    have h : ξ {c | ¬ pz c < ∞} = 0 := ae_iff.1 hpz_lt
    convert h using 2
    ext c; simp
  have h_rect_wd {A : Set α} {B : Set β} {D : Set γ}
      (hA : MeasurableSet A) (hB : MeasurableSet B) (hD : MeasurableSet D) :
      (ρ.withDensity fL) (A ×ˢ (B ×ˢ D)) = (ρ.withDensity fR) (A ×ˢ (B ×ˢ D)) := by
    have hS : MeasurableSet (A ×ˢ (B ×ˢ D)) := hA.prod (hB.prod hD)
    rw [withDensity_apply _ hS, withDensity_apply _ hS]
    exact h_rect A B D hA hB hD
  let Cβγ : Set (Set (β × γ)) :=
    Set.image2 (· ×ˢ ·) {s : Set β | MeasurableSet s} {t : Set γ | MeasurableSet t}
  let Cπ : Set (Set (α × β × γ)) :=
    Set.image2 (· ×ˢ ·) {s : Set α | MeasurableSet s} Cβγ
  have hCβγ_pi : IsPiSystem Cβγ :=
    IsPiSystem.prod isPiSystem_measurableSet isPiSystem_measurableSet
  have hCπ_pi : IsPiSystem Cπ :=
    IsPiSystem.prod isPiSystem_measurableSet hCβγ_pi
  have hCβγ_span : IsCountablySpanning Cβγ :=
    isCountablySpanning_measurableSet.prod isCountablySpanning_measurableSet
  have hCβγ_gen : generateFrom Cβγ = (inferInstance : MeasurableSpace (β × γ)) :=
    generateFrom_prod
  have hCπ_gen : generateFrom Cπ = (inferInstance : MeasurableSpace (α × β × γ)) :=
    generateFrom_eq_prod
      (C := {s : Set α | MeasurableSet s}) (D := Cβγ)
      (by simp) hCβγ_gen isCountablySpanning_measurableSet hCβγ_span
  have hpz_le_meas (n : ℕ) : MeasurableSet {c | pz c ≤ (n : ENNReal)} :=
    measurableSet_le hpz measurable_const
  have hpz_top_meas : MeasurableSet {c | pz c = (∞ : ENNReal)} :=
    hpz (measurableSet_singleton _)
  let Bn (n : ℕ) : Set (α × β × γ) :=
    spanningSets μ n ×ˢ
      (spanningSets ν n ×ˢ
        (spanningSets ξ n ∩ {c | pz c ≤ (n : ENNReal)} ∪
          {c | pz c = (∞ : ENNReal)}))
  have hBn_mem (n : ℕ) : Bn n ∈ Cπ :=
    ⟨spanningSets μ n, measurableSet_spanningSets μ n,
      spanningSets ν n ×ˢ
        (spanningSets ξ n ∩ {c | pz c ≤ (n : ENNReal)} ∪
          {c | pz c = (∞ : ENNReal)}),
      ⟨spanningSets ν n, measurableSet_spanningSets ν n,
        spanningSets ξ n ∩ {c | pz c ≤ (n : ENNReal)} ∪
          {c | pz c = (∞ : ENNReal)},
        ((measurableSet_spanningSets ξ n).inter (hpz_le_meas n)).union hpz_top_meas,
        rfl⟩,
      rfl⟩
  have hBn_span : ⋃ n, Bn n = Set.univ := by
    ext ⟨a, b, c⟩
    simp only [Set.mem_iUnion, Set.mem_univ]
    constructor
    · intro; trivial
    · intro
      obtain ⟨nα, ha⟩ : ∃ n, a ∈ spanningSets μ n := by
        have : a ∈ ⋃ n, spanningSets μ n := by
          rw [iUnion_spanningSets]; exact Set.mem_univ _
        exact Set.mem_iUnion.mp this
      obtain ⟨nβ, hb⟩ : ∃ n, b ∈ spanningSets ν n := by
        have : b ∈ ⋃ n, spanningSets ν n := by
          rw [iUnion_spanningSets]; exact Set.mem_univ _
        exact Set.mem_iUnion.mp this
      obtain ⟨nγ, hc⟩ : ∃ n, c ∈ spanningSets ξ n := by
        have : c ∈ ⋃ n, spanningSets ξ n := by
          rw [iUnion_spanningSets]; exact Set.mem_univ _
        exact Set.mem_iUnion.mp this
      by_cases htop : pz c = (∞ : ENNReal)
      · refine ⟨nα ⊔ nβ ⊔ nγ, ?_, ?_, Or.inr htop⟩
        · exact monotone_spanningSets μ (le_sup_of_le_left le_sup_left) ha
        · exact monotone_spanningSets ν (le_sup_of_le_left le_sup_right) hb
      · have hne : pz c ≠ ∞ := htop
        obtain ⟨n0, hn0⟩ := ENNReal.exists_nat_gt hne
        have hn0' : pz c ≤ (n0 : ENNReal) := le_of_lt hn0
        refine ⟨nα ⊔ nβ ⊔ nγ ⊔ n0, ?_, ?_, Or.inl ⟨?_, ?_⟩⟩
        · exact monotone_spanningSets μ
            (le_sup_of_le_left (le_sup_of_le_left le_sup_left)) ha
        · exact monotone_spanningSets ν
            (le_sup_of_le_left (le_sup_of_le_left le_sup_right)) hb
        · exact monotone_spanningSets ξ (le_sup_of_le_left le_sup_right) hc
        · exact hn0'.trans (Nat.cast_le.mpr le_sup_right)
  have hpxyz_int : ∫⁻ p, pxyz p ∂ρ = 1 := by
    have h : (ρ.withDensity pxyz) Set.univ = ∫⁻ p, pxyz p ∂ρ := by
      rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
    have : IsProbabilityMeasure (π.map (x, (y, z))) :=
      Measure.isProbabilityMeasure_map hPxyz.aemeasurable
    rw [← hlaw_xyz, measure_univ] at h
    exact h.symm
  have hBn_fin (n : ℕ) : (ρ.withDensity fL) (Bn n) ≠ ∞ := by
    have hS : MeasurableSet (Bn n) :=
      (measurableSet_spanningSets μ n).prod
        ((measurableSet_spanningSets ν n).prod
          (((measurableSet_spanningSets ξ n).inter (hpz_le_meas n)).union hpz_top_meas))
    rw [withDensity_apply _ hS]
    set A := spanningSets μ n
    set B := spanningSets ν n
    set Dtrunc := spanningSets ξ n ∩ {c | pz c ≤ (n : ENNReal)}
    set Dtop := {c | pz c = (∞ : ENNReal)}
    have hA : MeasurableSet A := measurableSet_spanningSets μ n
    have hB : MeasurableSet B := measurableSet_spanningSets ν n
    have hDt : MeasurableSet Dtrunc :=
      (measurableSet_spanningSets ξ n).inter (hpz_le_meas n)
    have hdisj : Disjoint (A ×ˢ (B ×ˢ Dtrunc)) (A ×ˢ (B ×ˢ Dtop)) :=
      Set.disjoint_left.2 fun p hp hptop => by
        have hle : pz p.2.2 ≤ (n : ENNReal) := hp.2.2.2
        have htop : pz p.2.2 = (∞ : ENNReal) := hptop.2.2
        simp [htop] at hle
    have hunion :
        A ×ˢ (B ×ˢ (Dtrunc ∪ Dtop)) =
          A ×ˢ (B ×ˢ Dtrunc) ∪ A ×ˢ (B ×ˢ Dtop) := by
      ext; simp [Set.mem_prod, Set.mem_union]
    have hsplit :
        ∫⁻ p in Bn n, fL p ∂ρ =
          ∫⁻ p in A ×ˢ (B ×ˢ Dtrunc), fL p ∂ρ +
            ∫⁻ p in A ×ˢ (B ×ˢ Dtop), fL p ∂ρ := by
      change ∫⁻ p in A ×ˢ (B ×ˢ (Dtrunc ∪ Dtop)), fL p ∂ρ = _
      rw [hunion, lintegral_union (hA.prod (hB.prod hpz_top_meas)) hdisj]
    have htop0 : ∫⁻ p in A ×ˢ (B ×ˢ Dtop), fL p ∂ρ = 0 := by
      refine setLIntegral_measure_zero _ _ ?_
      have : ρ (A ×ˢ (B ×ˢ Dtop)) = 0 := by
        simp [ρ, Measure.prod_prod, hpz_top_null]
      exact this
    have htrunc_le :
        ∫⁻ p in A ×ˢ (B ×ˢ Dtrunc), fL p ∂ρ ≤ (n : ENNReal) * ∫⁻ p, pxyz p ∂ρ := by
      have hpt : ∀ p ∈ A ×ˢ (B ×ˢ Dtrunc), fL p ≤ (n : ENNReal) * pxyz p := by
        intro p hp
        have hpz_le : pz p.2.2 ≤ (n : ENNReal) := hp.2.2.2
        -- fL p = pxyz (p.1, p.2) * pz p.2.2
        change pxyz (p.1, p.2) * pz p.2.2 ≤ (n : ENNReal) * pxyz (p.1, p.2)
        calc
          pxyz (p.1, p.2) * pz p.2.2
              ≤ pxyz (p.1, p.2) * (n : ENNReal) := mul_le_mul' le_rfl hpz_le
          _ = (n : ENNReal) * pxyz (p.1, p.2) := mul_comm _ _
      refine (setLIntegral_mono' (hA.prod (hB.prod hDt)) hpt).trans ?_
      have :
          ∫⁻ p in A ×ˢ (B ×ˢ Dtrunc), (n : ENNReal) * pxyz p ∂ρ ≤
            ∫⁻ p, (n : ENNReal) * pxyz p ∂ρ :=
        setLIntegral_le_lintegral _ _
      refine this.trans_eq ?_
      exact lintegral_const_mul'' _ hpxyz.aemeasurable
    have : ∫⁻ p in Bn n, fL p ∂ρ ≤ (n : ENNReal) := by
      rw [hsplit, htop0, add_zero]
      refine htrunc_le.trans_eq ?_
      rw [hpxyz_int, mul_one]
    exact (lt_of_le_of_lt this (ENNReal.natCast_lt_top n)).ne
  have h_ae : fL =ᵐ[ρ] fR := by
    refine (withDensity_eq_iff_of_sigmaFinite
      hfL.aemeasurable hfR.aemeasurable).1 ?_
    refine Measure.ext_of_generateFrom_of_iUnion (μ := ρ.withDensity fL)
      (ν := ρ.withDensity fR) Cπ Bn hCπ_gen.symm hCπ_pi hBn_span hBn_mem hBn_fin ?_
    intro S hS
    obtain ⟨A, hA, E, hE, rfl⟩ := hS
    obtain ⟨B, hB, D, hD, rfl⟩ := hE
    exact h_rect_wd hA hB hD
  have h_ae' : ∀ᵐ a ∂μ, ∀ᵐ bc ∂(ν.prod ξ), fL (a, bc) = fR (a, bc) :=
    (Measure.ae_prod_iff_ae_ae (μ := μ) (ν := ν.prod ξ)
      (measurableSet_eq_fun hfL hfR)).1 h_ae
  have hmul : ∀ᵐ b ∂ν, ∀ᵐ c ∂ξ,
      π.prob (y, z) (b, c) = π.condProb (y, z) (b, c) * π.prob z c :=
    All_Eq_MulProbCond.of.PSpace_Joint hPyz
  have htot_yz : ∫⁻ bc, π.prob (y, z) bc ∂(ν.prod ξ) = 1 := by
    have h : ((ν.prod ξ).withDensity (π.prob (y, z))) Set.univ =
        ∫⁻ bc, π.prob (y, z) bc ∂(ν.prod ξ) := by
      rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
    have : IsProbabilityMeasure (π.map (y, z)) :=
      Measure.isProbabilityMeasure_map hPyz.aemeasurable
    rw [← hlaw_yz, measure_univ] at h
    exact h.symm
  have hfin_yz : ∀ᵐ b ∂ν, ∀ᵐ c ∂ξ, π.prob (y, z) (b, c) < ⊤ :=
    Measure.ae_ae_of_ae_prod (ae_lt_top hpyz (by rw [htot_yz]; norm_num))
  have hden_yz : π.map (fun ω ↦ ((x, (y, z)) ω).2) = π.map (y, z) := by congr
  have hden_z : π.map (fun ω ↦ ((x, z) ω).2) = π.map z := by congr
  have hmul3 : ∀ᵐ a ∂μ, ∀ᵐ b ∂ν, ∀ᵐ c ∂ξ,
      π.prob (y, z) (b, c) = π.condProb (y, z) (b, c) * π.prob z c := by
    filter_upwards with a
    exact hmul
  have hfin_yz3 : ∀ᵐ a ∂μ, ∀ᵐ b ∂ν, ∀ᵐ c ∂ξ, π.prob (y, z) (b, c) < ⊤ := by
    filter_upwards with a
    exact hfin_yz
  have hfin_z3 : ∀ᵐ a ∂μ, ∀ᵐ b ∂ν, ∀ᵐ c ∂ξ, π.prob z c < ⊤ := by
    filter_upwards with a
    filter_upwards with b
    exact hpz_lt
  filter_upwards [h_ae', hmul3, hfin_yz3, hfin_z3] with a ha hmul hfin_yz hfin_z
  have hb :=
    (Measure.ae_prod_iff_ae_ae (μ := ν) (ν := ξ)
      (measurableSet_eq_fun (hfL.comp measurable_prodMk_left)
        (hfR.comp measurable_prodMk_left))).1 ha
  filter_upwards [hb, hmul, hfin_yz, hfin_z] with b hb' hmul hfin_yz hfin_z
  filter_upwards [hb', hmul, hfin_yz, hfin_z] with c hc hmul hfin_yz hfin_z
  intro hne
  have hpz_ne : π.prob z c ≠ 0 := by
    intro hz0
    apply hne
    rw [hmul, hz0, mul_zero]
  have hdefL :
      π.condProb (x, (y, z)) (a, (b, c)) =
        π.prob (x, (y, z)) (a, (b, c)) / π.prob (y, z) (b, c) := by
    unfold Measure.condProb Measure.prob
    rw [hden_yz]
  have hdefR :
      π.condProb (x, z) (a, c) =
        π.prob (x, z) (a, c) / π.prob z c := by
    unfold Measure.condProb Measure.prob
    rw [hden_z]
  rw [hdefL, hdefR]
  refine (ENNReal.div_eq_div_iff hpz_ne hfin_z.ne hne hfin_yz.ne).2 ?_
  simpa [fL, fR, mul_comm (π.prob z c), mul_comm (π.prob (y, z) (b, c))] using hc


-- created on 2020-12-16
-- updated on 2026-09-22
