import Lemma.Random.Prob_Cond.eq.Div.of.SinglePSpace
import Lemma.Random.SinglePSpace.of.Measurable
import Lemma.Random.SinglePSpace.of.Measurable.Measurable
import Lemma.Random.Indep.of.Lt0.All_Indep_GetSlice.All_Measurable
import Mathlib.Probability.Independence.Conditional
import Notation.Fun
open MeasureTheory ProbabilityTheory Measure Random Fun
open scoped ProbabilityTheory


private lemma atom_comap
  [MeasurableSpace Ω] [MeasurableSpace γ]
  {z : Ω → γ} {w : γ} {T : Set Ω}
-- given
  (hT : MeasurableSet[MeasurableSpace.comap z inferInstance] T) :
-- imply
  z ⁻¹' {w} ∩ T = ∅ ∨ z ⁻¹' {w} ⊆ T := by
-- proof
  obtain ⟨W, _, rfl⟩ := hT
  if hw : w ∈ W then
    refine Or.inr ?_
    intro ω hω
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hω ⊢
    exact hω ▸ hw
  else
    refine Or.inl (Set.eq_empty_iff_forall_notMem.mpr ?_)
    intro ω hω
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff] at hω
    exact hw (hω.1 ▸ hω.2)

private lemma condExp_eq_div_on_atom
  [MeasurableSpace Ω] [StandardBorelSpace Ω]
  [MeasurableSpace γ] [MeasurableSingletonClass γ]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {z : Ω → γ} {w : γ} {S : Set Ω}
-- given
  (hz : Measurable z)
  (hS : MeasurableSet S)
  (hC0 : π (z ⁻¹' {w}) ≠ 0) :
-- imply
  ∀ ω ∈ z ⁻¹' {w},
    (π⟦S | MeasurableSpace.comap z inferInstance⟧) ω =
      π.real (S ∩ z ⁻¹' {w}) / π.real (z ⁻¹' {w}) := by
-- proof
  set C : Set Ω := z ⁻¹' {w}
  set f : Ω → ℝ := π⟦S | MeasurableSpace.comap z inferInstance⟧
  have hf : Measurable[MeasurableSpace.comap z inferInstance] f := stronglyMeasurable_condExp.measurable
  have hC : MeasurableSet[MeasurableSpace.comap z inferInstance] C := ⟨{w}, measurableSet_singleton w, rfl⟩
  intro ω hω
  obtain ⟨ω0, hω0⟩ : C.Nonempty := ⟨ω, hω⟩
  have hconst : ∀ ω' ∈ C, f ω' = f ω0 := by
    intro ω' hω'
    exact (atom_comap (z := z) (w := w) (hf (measurableSet_singleton _))).resolve_left
      (fun hempty => (Set.eq_empty_iff_forall_notMem.mp hempty) _ ⟨hω0, rfl⟩) hω'
  apply (hconst ω hω).trans
  have hfS : Integrable (S.indicator fun _ => (1 : ℝ)) π :=
    (integrable_const (1 : ℝ)).indicator hS
  have hint : ∫ ω' in C, f ω' ∂π = π.real (S ∩ C) := by
    have h := setIntegral_condExp (m := MeasurableSpace.comap z inferInstance) (μ := π)
      (f := S.indicator fun _ => (1 : ℝ)) hz.comap_le hfS hC
    unfold f
    rw [h, setIntegral_indicator hS, integral_const, smul_eq_mul, mul_one]
    rw [Measure.real, Measure.restrict_apply_univ, Measure.real, Set.inter_comm]
  have hintc : ∫ ω' in C, f ω' ∂π = f ω0 * π.real C := by
    have hCm : MeasurableSet C := hz (measurableSet_singleton w)
    rw [setIntegral_congr_fun hCm fun ω' hω' => hconst ω' hω',
      setIntegral_const, smul_eq_mul, mul_comm]
  have hCne : π.real C ≠ 0 := by
    have htop : π C ≠ ⊤ := measure_ne_top _ _
    rw [Measure.real, ENNReal.toReal_ne_zero]
    exact ⟨hC0, htop⟩
  have : f ω0 * π.real C = π.real (S ∩ C) := hintc.symm.trans hint
  exact (eq_div_iff hCne).2 (mul_comm (f ω0) (π.real C) ▸ this)

private lemma mul_measure_of_condIndep
  [MeasurableSpace Ω] [StandardBorelSpace Ω]
  [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β]
  [MeasurableSingletonClass γ]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {x : Ω → α} {y : Ω → β} {z : Ω → γ}
-- given
  (hx : Measurable x) (hy : Measurable y) (hz : Measurable z)
  (hCI : x ⟂ᵢ[z, hz; π] y)
  (u : α) (v : β) (w : γ) :
-- imply
  π (x ⁻¹' {u} ∩ y ⁻¹' {v} ∩ z ⁻¹' {w}) * π (z ⁻¹' {w}) =
    π (x ⁻¹' {u} ∩ z ⁻¹' {w}) * π (y ⁻¹' {v} ∩ z ⁻¹' {w}) := by
-- proof
  set A : Set Ω := x ⁻¹' {u}
  set B : Set Ω := y ⁻¹' {v}
  set C : Set Ω := z ⁻¹' {w}
  have hA : MeasurableSet A := hx (measurableSet_singleton u)
  have hB : MeasurableSet B := hy (measurableSet_singleton v)
  have hCμ : MeasurableSet C := hz (measurableSet_singleton w)
  have hC : MeasurableSet[MeasurableSpace.comap z inferInstance] C := ⟨{w}, measurableSet_singleton w, rfl⟩
  have hleC : π C ≤ 1 := by
    rw [← measure_univ (μ := π)]
    exact measure_mono (Set.subset_univ C)
  have htopC : π C ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hleC
  if hC0 : π C = 0 then
    have hAC : π (A ∩ C) = 0 := measure_mono_null Set.inter_subset_right hC0
    have hBC : π (B ∩ C) = 0 := measure_mono_null Set.inter_subset_right hC0
    have hABC : π (A ∩ B ∩ C) = 0 :=
      measure_mono_null (Set.inter_subset_right (s := A ∩ B)) hC0
    simp [A, B, C] at *
    simp [hC0, hAC, hBC, hABC]
  else
    have hprod :=
      (condIndepFun_iff_condExp_inter_preimage_eq_mul (m' := MeasurableSpace.comap z inferInstance) (hm' := hz.comap_le)
        hx hy).1 hCI {u} {v}
        (measurableSet_singleton u) (measurableSet_singleton v)
    have hdivS (S : Set Ω) (hS : MeasurableSet S) :
      ∀ ω ∈ C, (π⟦S | MeasurableSpace.comap z inferInstance⟧) ω = π.real (S ∩ C) / π.real C :=
      condExp_eq_div_on_atom hz hS hC0
    have hfAB : Integrable ((A ∩ B).indicator fun _ => (1 : ℝ)) π :=
      (integrable_const (1 : ℝ)).indicator (hA.inter hB)
    have hint :
      ∫ ω in C, (π⟦A ∩ B | MeasurableSpace.comap z inferInstance⟧) ω ∂π = π.real (A ∩ B ∩ C) := by
      have h := setIntegral_condExp (m := MeasurableSpace.comap z inferInstance) (μ := π)
        (f := (A ∩ B).indicator fun _ => (1 : ℝ)) hz.comap_le hfAB hC
      have hinter : C ∩ (A ∩ B) = A ∩ B ∩ C := by
        ext ω
        simp [and_comm]
      rw [h, setIntegral_indicator (hA.inter hB), integral_const, smul_eq_mul, mul_one]
      rw [Measure.real, Measure.restrict_apply_univ, Measure.real, hinter]
    have hintp :
      ∫ ω in C, (π⟦A | MeasurableSpace.comap z inferInstance⟧) ω * (π⟦B | MeasurableSpace.comap z inferInstance⟧) ω ∂π =
        π.real (A ∩ C) / π.real C * (π.real (B ∩ C) / π.real C) * π.real C := by
      have hfun : ∀ ω ∈ C,
          (π⟦A | MeasurableSpace.comap z inferInstance⟧) ω *
            (π⟦B | MeasurableSpace.comap z inferInstance⟧) ω =
            π.real (A ∩ C) / π.real C * (π.real (B ∩ C) / π.real C) := by
        intro ω hω
        rw [hdivS A hA ω hω, hdivS B hB ω hω]
      rw [setIntegral_congr_fun hCμ fun ω hω => hfun ω hω, setIntegral_const,
        smul_eq_mul]
      simp only [Measure.real]
      ring
    have heq : π.real (A ∩ B ∩ C) =
        π.real (A ∩ C) / π.real C * (π.real (B ∩ C) / π.real C) * π.real C := by
      have hcongr : (π⟦A ∩ B | MeasurableSpace.comap z inferInstance⟧) =ᵐ[π.restrict C]
        fun ω =>
          (π⟦A | MeasurableSpace.comap z inferInstance⟧) ω *
            (π⟦B | MeasurableSpace.comap z inferInstance⟧) ω :=
        ae_restrict_of_ae hprod
      exact hint.symm.trans
        ((setIntegral_congr_ae hCμ ((ae_restrict_iff' hCμ).1 hcongr)).trans hintp)
    have hCne : π.real C ≠ 0 := by
      rw [Measure.real, ENNReal.toReal_ne_zero]
      exact ⟨hC0, htopC⟩
    have hmulR : π.real (A ∩ B ∩ C) * π.real C =
        π.real (A ∩ C) * π.real (B ∩ C) := by
      field_simp [hCne] at heq ⊢
      linarith
    have hfin (S : Set Ω) : π S ≠ ⊤ := measure_ne_top _ _
    have hR (S : Set Ω) : ENNReal.ofReal (π.real S) = π S := by
      rw [Measure.real, ENNReal.ofReal_toReal (hfin S)]
    calc
      _ = ENNReal.ofReal (π.real (A ∩ B ∩ C)) * ENNReal.ofReal (π.real C) := by
        rw [hR, hR]
      _ = ENNReal.ofReal (π.real (A ∩ B ∩ C) * π.real C) := by
        rw [← ENNReal.ofReal_mul (show 0 ≤ π.real (A ∩ B ∩ C) from ENNReal.toReal_nonneg)]
      _ = ENNReal.ofReal (π.real (A ∩ C) * π.real (B ∩ C)) := by
        rw [hmulR]
      _ = ENNReal.ofReal (π.real (A ∩ C)) * ENNReal.ofReal (π.real (B ∩ C)) := by
        rw [ENNReal.ofReal_mul (show 0 ≤ π.real (A ∩ C) from ENNReal.toReal_nonneg)]
      _ = π (A ∩ C) * π (B ∩ C) := by
        rw [hR, hR]

/--
First-order Markov factorization: if `s[t + 1]` is conditionally independent of the
prefix `s[:t]` given `s[t]` at every time, then
`ℙ(s[k + 1] | s[k]) * ℙ(s[k] | s[0]) = ℙ(s[k + 1] ∧ s[k] | s[0])`.

The Markov hypothesis projects from the prefix `s[:k]` down to `s[0]` by
[conditional independence of `s[k + 1]` and `s[0]` given `s[k]`](?module=Random.Indep.of.Lt0.All_Indep_GetSlice.All_Measurable).

Python: [Random.MulProbS_Cond.eq.Prob_CondJoint.of.All_Indep_GetSlice.All_Measurable](?module=Random.MulProbS_Cond.eq.Prob_CondJoint.of.All_Indep_GetSlice.All_Measurable).
-/
@[path]
private lemma main
  [MeasurableSpace Ω] [StandardBorelSpace Ω]
  [CountableMeasure 𝒮]
  [Countable 𝒮] [MeasurableSingletonClass 𝒮]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {s : ℕ ⇀ Ω → 𝒮}
  {k : ℕ}
-- given
  (hs : ∀ t, Measurable s[t])
  (hmarkov : ∀ t, s[t + 1] ⟂ᵢ[s t, hs t; π] s[:t])
  («\sf{s}» : ℕ ⇀ 𝒮) :
-- imply
  have : SinglePSpace π (s[k + 1], s[k]) :=
    SinglePSpace.of.Measurable.Measurable (hs (k + 1)) (hs k)
  have : SinglePSpace π (s[k], s[0]) :=
    SinglePSpace.of.Measurable.Measurable (hs k) (hs 0)
  have : SinglePSpace π ((s[k + 1], s[k]), s[0]) :=
    SinglePSpace.of.Measurable.Measurable ((hs (k + 1)).prodMk (hs k)) (hs 0)
  ℙ[π](s[k + 1] = «\sf{s}»[k + 1] | s[k] = «\sf{s}»[k]) *
    ℙ[π](s[k] = «\sf{s}»[k] | s[0] = «\sf{s}»[0]) =
    ℙ[π](s[k + 1] = «\sf{s}»[k + 1] ∧ s[k] = «\sf{s}»[k] | s[0] = «\sf{s}»[0]) := by
-- proof
  intro hPsk1k hPsk0 hPjoint
  set sk1 := «\sf{s}»[k + 1]
  set sk := «\sf{s}»[k]
  set s0 := «\sf{s}»[0]
  set A : Set Ω := s[k] ⁻¹' {sk}
  set B : Set Ω := s[k + 1] ⁻¹' {sk1}
  set C : Set Ω := s[0] ⁻¹' {s0}
  have hdiv_trans :
    ℙ[π](s[k + 1] = sk1 | s[k] = sk) = π (B ∩ A) / π A :=
    Prob_Cond.eq.Div.of.SinglePSpace hPsk1k sk1 sk
  have hdiv_marg :
    ℙ[π](s[k] = sk | s[0] = s0) = π (A ∩ C) / π C :=
    Prob_Cond.eq.Div.of.SinglePSpace hPsk0 sk s0
  have hdiv_joint :
    ℙ[π](s[k + 1] = sk1 ∧ s[k] = sk | s[0] = s0) = π (B ∩ A ∩ C) / π C := by
    apply Eq.trans _
      ((Prob_Cond.eq.Div.of.SinglePSpace (x := (s[k + 1], s[k])) (y := s[0]) hPjoint (sk1, sk) s0).trans
        (congrArg (fun t => π t / π C) _))
    rfl
    ext ω
    simp [A, B, C, Prod.ext_iff, and_comm, and_left_comm,
      show (s[k + 1], s[k]) ω = (s[k + 1] ω, s[k] ω) from rfl]
  rw [hdiv_trans, hdiv_marg, hdiv_joint]
  have hBAC_le_AC : B ∩ A ∩ C ⊆ A ∩ C := by
    intro ω hω
    exact ⟨hω.1.2, hω.2⟩
  have htopA : π A ≠ ⊤ := measure_ne_top _ _
  have htopAC : π (A ∩ C) ≠ ⊤ := measure_ne_top _ _
  if hC0 : π C = 0 then
    have hAC_null : π (A ∩ C) = 0 :=
      measure_mono_null Set.inter_subset_right hC0
    have hBAC_null : π (B ∩ A ∩ C) = 0 :=
      measure_mono_null (fun _ hω => hω.2) hC0
    simp [hC0, hAC_null, hBAC_null]
  else if hAC0 : π (A ∩ C) = 0 then
    have : π (B ∩ A ∩ C) = 0 := measure_mono_null hBAC_le_AC hAC0
    simp [hAC0, this]
  else if hk0 : k = 0 then
    have hCA : C = A := by
      ext ω
      simp [A, C, sk, s0, hk0]
    have hA0 : π A ≠ 0 := by
      simpa [hCA, Set.inter_self] using hAC0
    rw [hCA, Set.inter_self]
    have hAA : B ∩ A ∩ A = B ∩ A := by
      rw [Set.inter_assoc, Set.inter_self]
    rw [hAA, div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv_cancel hA0 htopA, mul_one]
  else
    have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    have hmul :=
      mul_measure_of_condIndep (hs (k + 1)) (hs 0) (hs k)
        (Indep.of.Lt0.All_Indep_GetSlice.All_Measurable hs hmarkov hkpos) sk1 s0 sk
    have hinter : B ∩ C ∩ A = B ∩ A ∩ C := by
      ext ω
      simp [and_comm, and_left_comm]
    have hinter' : C ∩ A = A ∩ C := Set.inter_comm _ _
    have hAne : π A ≠ 0 := by
      intro hA0
      exact hAC0 (measure_mono_null Set.inter_subset_left hA0)
    have hratio : π (B ∩ A) / π A = π (B ∩ A ∩ C) / π (A ∩ C) := by
      have : π (B ∩ C ∩ A) * π A = π (B ∩ A) * π (C ∩ A) := hmul
      rw [hinter, hinter'] at this
      rw [div_eq_mul_inv, div_eq_mul_inv]
      calc
        _ = π (B ∩ A) * (π A)⁻¹ * (π (A ∩ C) * (π (A ∩ C))⁻¹) := by
          rw [ENNReal.mul_inv_cancel hAC0 htopAC, mul_one]
        _ = π (B ∩ A) * π (A ∩ C) * (π A)⁻¹ * (π (A ∩ C))⁻¹ := by ac_rfl
        _ = π (B ∩ A ∩ C) * π A * (π A)⁻¹ * (π (A ∩ C))⁻¹ := by
          rw [← this]
        _ = π (B ∩ A ∩ C) * (π (A ∩ C))⁻¹ := by
          rw [mul_assoc (π (B ∩ A ∩ C)), ENNReal.mul_inv_cancel hAne htopA, mul_one]
    calc
      _ = π (B ∩ A ∩ C) / π (A ∩ C) * (π (A ∩ C) / π C) := by
        rw [hratio]
      _ = π (B ∩ A ∩ C) / π C := by
        rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_assoc]
        rw [← mul_assoc (π (A ∩ C))⁻¹, ENNReal.inv_mul_cancel hAC0 htopAC, one_mul]


-- created on 2023-03-30
-- updated on 2026-11-13
