import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.TheoryOfProbability.code.MarkovChainFDD
open MeasureTheory ProbabilityTheory ENNReal Set


/--
[markovFDD_measurable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/MarkovChainFDD.lean)
-/
@[path]
lemma markovFDD_measurable
  [MeasurableSpace S]
  {kappa : Kernel S S}
  [IsMarkovKernel kappa]
  {n : Nat}
-- given
  (A : Fin (n + 1) -> Set S)
  (hA : forall i, MeasurableSet (A i)) :
-- imply
  Measurable (fun x => markovFDD (kappa x) kappa n A) := by
-- proof
  induction n with
  | zero => simp only [markovFDD]; exact Kernel.measurable_coe kappa (hA 0)
  | succ m ih =>
    simp only [markovFDD]
    show Measurable (fun x => ∫⁻ y in A 0, markovFDD (kappa y) kappa m (fun i => A i.succ) ∂(kappa x))
    have hg : Measurable (fun x => markovFDD (kappa x) kappa m (fun i => A i.succ)) :=
      ih (fun i => A i.succ) (fun i => hA i.succ)
    have : (fun x => ∫⁻ y in A 0, markovFDD (kappa y) kappa m (fun i => A i.succ) ∂(kappa x)) =
      (fun x => ∫⁻ y, (A 0).indicator
        (fun y => markovFDD (kappa y) kappa m (fun i => A i.succ)) y ∂(kappa x)) := by
      ext x; rw [← lintegral_indicator (hA 0)]
    rw [this]
    exact (Measurable.lintegral_kernel_prod_right ((hg.indicator (hA 0)).comp measurable_snd))

/--
[comap_sigma_mono](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/MarkovChainFDD.lean)
-/
@[path]
lemma comap_sigma_mono
  [MeasurableSpace Omega]
  [MeasurableSpace S]
  {k : Nat}
-- given
  (X : Nat -> Omega -> S) :
-- imply
  MeasurableSpace.comap (fun omega => fun i : Fin (k + 1) => X i omega) MeasurableSpace.pi ≤ MeasurableSpace.comap (fun omega => fun i : Fin (k + 2) => X i omega) MeasurableSpace.pi := by
-- proof
  let phi : (Fin (k + 2) -> S) -> (Fin (k + 1) -> S) := fun f i => f (Fin.castSucc i)
  have hphi : @Measurable _ _ MeasurableSpace.pi MeasurableSpace.pi phi :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply _)
  have h_factor : (fun omega => fun i : Fin (k + 1) => X (↑i) omega) =
    phi ∘ (fun omega => fun i : Fin (k + 2) => X (↑i) omega) := by
    ext omega i; simp [phi, Fin.castSucc]
  rw [h_factor, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono hphi.comap_le

/--
[comap_inter_preimage](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/MarkovChainFDD.lean)
-/
@[path]
lemma comap_inter_preimage
  [MeasurableSpace Omega]
  [MeasurableSpace S]
  {k : Nat}
  {C : Set Omega}
  {B : Set S}
-- given
  (X : Nat -> Omega -> S)
  (hB : MeasurableSet B)
  (hC : @MeasurableSet Omega (MeasurableSpace.comap (fun omega => fun i : Fin (k + 1) => X i omega) MeasurableSpace.pi) C) :
-- imply
  @MeasurableSet Omega (MeasurableSpace.comap (fun omega => fun i : Fin (k + 2) => X i omega) MeasurableSpace.pi) (C ∩ X (k + 1) ⁻¹' B) := by
-- proof
  exact MeasurableSet.inter (comap_sigma_mono X k C hC)
    (by rw [MeasurableSpace.measurableSet_comap]
      exact ⟨(fun f : Fin (k + 2) -> S => f ⟨k + 1, by omega⟩) ⁻¹' B,
        (measurable_pi_apply _) hB, by ext omega; simp⟩)

/--
[lintegral_measurable_extension](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/MarkovChainFDD.lean)
-/
@[path]
lemma lintegral_measurable_extension
  [MeasurableSpace Omega]
  [MeasurableSpace S]
  {P : Measure Omega}
  [IsProbabilityMeasure P]
  {kappa : Kernel S S}
  [IsMarkovKernel kappa]
  {k : Nat}
  {C : Set Omega}
-- given
  (X : Nat -> Omega -> S)
  (hmeas : forall i, Measurable (X i))
  (hmarkov : forall (k : Nat) (B : Set S), MeasurableSet B -> forall (C : Set Omega), @MeasurableSet Omega (MeasurableSpace.comap (fun omega => fun i : Fin (k + 1) => X i omega) MeasurableSpace.pi) C -> ∫⁻ omega in C, (X (k + 1) ⁻¹' B).indicator (fun _ => (1 : ENNReal)) omega ∂P = ∫⁻ omega in C, kappa (X k omega) B ∂P)
  (hC_comap : @MeasurableSet Omega (MeasurableSpace.comap (fun omega => fun i : Fin (k + 1) => X i omega) MeasurableSpace.pi) C)
  (f : S -> ENNReal)
  (hf : Measurable f) :
-- imply
  ∫⁻ omega in C, f (X (k + 1) omega) ∂P = ∫⁻ omega in C, (∫⁻ y, f y ∂kappa (X k omega)) ∂P := by
-- proof
  have h_eq : (P.restrict C).map (X (k + 1)) =
    ((P.restrict C).map (X k)).bind (fun x => kappa x) := by
    ext B hB
    rw [Measure.map_apply (hmeas (k + 1)) hB,
      Measure.bind_apply hB (Kernel.measurable kappa).aemeasurable,
      lintegral_map (Kernel.measurable_coe kappa hB) (hmeas k),
      Measure.restrict_apply (hmeas (k + 1) hB)]
    have h := hmarkov k B hB C hC_comap
    rw [lintegral_indicator ((hmeas (k + 1)) hB), setLIntegral_one,
      Measure.restrict_apply ((hmeas (k + 1)) hB)] at h
    exact h
  calc ∫⁻ omega in C, f (X (k + 1) omega) ∂P
    = ∫⁻ y, f y ∂((P.restrict C).map (X (k + 1))) := by
      rw [lintegral_map hf (hmeas (k + 1))]
    _ = ∫⁻ y, f y ∂(((P.restrict C).map (X k)).bind (fun x => kappa x)) := by
      rw [h_eq]
    _ = ∫⁻ x, (∫⁻ y, f y ∂kappa x) ∂((P.restrict C).map (X k)) := by
      rw [Measure.lintegral_bind (Kernel.measurable kappa).aemeasurable hf.aemeasurable]
    _ = ∫⁻ omega in C, (∫⁻ y, f y ∂kappa (X k omega)) ∂P := by
      rw [lintegral_map _ (hmeas k)]
      exact Measurable.lintegral_kernel_prod_right (hf.comp measurable_snd)

/--
[set_lintegral_inter_preimage](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/MarkovChainFDD.lean)
-/
@[path]
lemma set_lintegral_inter_preimage
  [MeasurableSpace Omega]
  [MeasurableSpace S]
  {P : Measure Omega}
  {A : Set S}
  {C : Set Omega}
-- given
  (X : Omega -> S)
  (hX : Measurable X)
  (hA : MeasurableSet A)
  (f : S -> ENNReal) :
-- imply
  ∫⁻ omega in C ∩ X ⁻¹' A, f (X omega) ∂P = ∫⁻ omega in C, A.indicator f (X omega) ∂P := by
-- proof
  have : forall omega, A.indicator f (X omega) = (X ⁻¹' A).indicator (fun omega => f (X omega)) omega := fun _ => rfl
  simp_rw [this]
  rw [lintegral_indicator (hX hA), Measure.restrict_restrict (hX hA), inter_comm]
set_option maxHeartbeats 1600000 in

/--
[markov_chain_fdd_aux](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/MarkovChainFDD.lean)
-/
@[path]
lemma markov_chain_fdd_aux
  [MeasurableSpace Omega]
  [MeasurableSpace S]
  {P : Measure Omega}
  [IsProbabilityMeasure P]
  {kappa : Kernel S S}
  [IsMarkovKernel kappa]
  {n : Nat}
  {j : Nat}
  {C : Set Omega}
-- given
  (X : Nat -> Omega -> S)
  (hmeas : forall i, Measurable (X i))
  (hmarkov : forall (k : Nat) (B : Set S), MeasurableSet B -> forall (C : Set Omega), @MeasurableSet Omega (MeasurableSpace.comap (fun omega => fun i : Fin (k + 1) => X i omega) MeasurableSpace.pi) C -> ∫⁻ omega in C, (X (k + 1) ⁻¹' B).indicator (fun _ => (1 : ENNReal)) omega ∂P = ∫⁻ omega in C, kappa (X k omega) B ∂P)
  (A : Fin (n + 1) -> Set S)
  (hA : forall i, MeasurableSet (A i))
  (hC_meas : MeasurableSet C)
  (hC_comap : @MeasurableSet Omega (MeasurableSpace.comap (fun omega => fun i : Fin (j + 1) => X i omega) MeasurableSpace.pi) C) :
-- imply
  P (C ∩ ⋂ i : Fin (n + 1), X (j + 1 + ↑i) ⁻¹' A i) = ∫⁻ omega in C, markovFDD (kappa (X j omega)) kappa n A ∂P := by
-- proof
  induction n generalizing j C with
  | zero =>
    simp only [markovFDD]
    have h_fin1 : ⋂ i : Fin 1, X (j + 1 + ↑i) ⁻¹' A i = X (j + 1) ⁻¹' A 0 := by
      ext omega; simp [Fin.forall_fin_one]
    rw [h_fin1]
    have h := hmarkov j (A 0) (hA 0) C hC_comap
    rw [lintegral_indicator (hmeas (j + 1) (hA 0)), setLIntegral_one,
      Measure.restrict_apply (hmeas (j + 1) (hA 0))] at h
    rw [inter_comm]; exact h
  | succ m ih =>
    have h_split : (⋂ i : Fin (m + 2), X (j + 1 + ↑i) ⁻¹' A i) =
      (X (j + 1) ⁻¹' A 0) ∩ (⋂ i : Fin (m + 1), X (j + 2 + ↑i) ⁻¹' A i.succ) := by
      ext omega
      simp only [mem_iInter, mem_inter_iff, mem_preimage]
      constructor
      · intro h
        exact ⟨by have := h 0; simp at this; exact this,
          fun i => by
            have := h i.succ; simp only [Fin.val_succ] at this
            convert this using 2; omega⟩
      · intro ⟨h0, hs⟩ i
        refine Fin.cases (by simpa using h0) (fun i => ?_) i
        simp only [Fin.val_succ]
        have := hs i; convert this using 2; omega
    rw [h_split, ← inter_assoc]
    set C' := C ∩ X (j + 1) ⁻¹' A 0
    have hC'_meas : MeasurableSet C' := hC_meas.inter (hmeas (j + 1) (hA 0))
    have hC'_comap : @MeasurableSet Omega (MeasurableSpace.comap
      (fun omega => fun i : Fin (j + 2) => X i omega) MeasurableSpace.pi) C' :=
      comap_inter_preimage X j C (A 0) (hA 0) hC_comap
    rw [ih (j + 1) (fun i => A i.succ) (fun i => hA i.succ) C' hC'_meas hC'_comap]
    simp only [markovFDD]
    set f := fun x => markovFDD (kappa x) kappa m (fun i => A i.succ) with hf_def
    have hf_meas : Measurable f := markovFDD_measurable kappa m _ (fun i => hA i.succ)
    rw [set_lintegral_inter_preimage P (X (j + 1)) (hmeas (j + 1)) (A 0) (hA 0) C f]
    rw [lintegral_measurable_extension P X hmeas kappa hmarkov j C hC_comap
      ((A 0).indicator f) (hf_meas.indicator (hA 0))]
    congr 1; ext omega
    rw [← lintegral_indicator (hA 0)]
set_option maxHeartbeats 1600000 in

/--
[markov_chain_fdd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/MarkovChainFDD.lean)
-/
@[path]
lemma markov_chain_fdd
  (in the sense expressed by `hmarkov`)
  [MeasurableSpace Omega]
  [MeasurableSpace S]
  {P : Measure Omega}
  [IsProbabilityMeasure P]
  {kappa : Kernel S S}
  [IsMarkovKernel kappa]
  {n : Nat}
-- given
  (X : Nat -> Omega -> S)
  (hmeas : forall i, Measurable (X i))
  (A : Fin (n + 1) -> Set S)
  (hA : forall i, MeasurableSet (A i))
  (hmarkov : forall (k : Nat) (B : Set S), MeasurableSet B -> forall (C : Set Omega), @MeasurableSet Omega (MeasurableSpace.comap (fun omega => fun i : Fin (k + 1) => X i omega) MeasurableSpace.pi) C -> ∫⁻ omega in C, (X (k + 1) ⁻¹' B).indicator (fun _ => (1 : ENNReal)) omega ∂P = ∫⁻ omega in C, kappa (X k omega) B ∂P) :
-- imply
  P (⋂ i : Fin (n + 1), X i ⁻¹' A i) = markovFDD (P.map (X 0)) kappa n A := by
-- proof
  induction n with
  | zero =>
    simp only [markovFDD]
    have h_fin1 : ⋂ i : Fin 1, X (↑i) ⁻¹' A i = X 0 ⁻¹' A 0 := by
      ext omega; simp [Fin.forall_fin_one]
    rw [h_fin1, ← Measure.map_apply (hmeas 0) (hA 0)]
  | succ m ih =>
    simp only [markovFDD]
    have h_split : (⋂ i : Fin (m + 2), X (↑i) ⁻¹' A i) =
      (X 0 ⁻¹' A 0) ∩ (⋂ i : Fin (m + 1), X (0 + 1 + ↑i) ⁻¹' A i.succ) := by
      ext omega
      simp only [mem_iInter, mem_inter_iff, mem_preimage]
      constructor
      · intro h
        exact ⟨by have := h 0; simp at this; exact this,
          fun i => by
            have := h i.succ; simp only [Fin.val_succ] at this
            convert this using 2; omega⟩
      · intro ⟨h0, hs⟩ i
        refine Fin.cases (by simpa using h0) (fun i => ?_) i
        simp only [Fin.val_succ]
        have := hs i; convert this using 2; omega
    rw [h_split]
    have hC_meas : MeasurableSet (X 0 ⁻¹' A 0) := hmeas 0 (hA 0)
    have hC_comap : @MeasurableSet Omega (MeasurableSpace.comap
      (fun omega => fun i : Fin 1 => X i omega) MeasurableSpace.pi) (X 0 ⁻¹' A 0) := by
      rw [MeasurableSpace.measurableSet_comap]
      exact ⟨(fun f : Fin 1 -> S => f 0) ⁻¹' A 0,
        (measurable_pi_apply _) (hA 0), by ext omega; simp⟩
    rw [markov_chain_fdd_aux P X hmeas kappa hmarkov m 0
      (fun i => A i.succ) (fun i => hA i.succ)
      (X 0 ⁻¹' A 0) hC_meas hC_comap]
    rw [← setLIntegral_map (hA 0)
      (markovFDD_measurable kappa m _ (fun i => hA i.succ)) (hmeas 0)]

/--
[markov_chain_finite_dimensional_distributions](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/MarkovChainFDD.lean)
-/
@[path]
lemma markov_chain_finite_dimensional_distributions
  (in the sense expressed by `hmarkov`)
  [MeasurableSpace Omega]
  [MeasurableSpace S]
  {P : Measure Omega}
  [IsProbabilityMeasure P]
  {kappa : Kernel S S}
  [IsMarkovKernel kappa]
  {n : Nat}
-- given
  (X : Nat -> Omega -> S)
  (hmeas : forall i, Measurable (X i))
  (A : Fin (n + 1) -> Set S)
  (hA : forall i, MeasurableSet (A i))
  (hmarkov : forall (k : Nat) (B : Set S), MeasurableSet B -> forall (C : Set Omega), @MeasurableSet Omega (MeasurableSpace.comap (fun omega => fun i : Fin (k + 1) => X i omega) MeasurableSpace.pi) C -> ∫⁻ omega in C, (X (k + 1) ⁻¹' B).indicator (fun _ => (1 : ENNReal)) omega ∂P = ∫⁻ omega in C, kappa (X k omega) B ∂P) :
-- imply
  P (⋂ i : Fin (n + 1), X i ⁻¹' A i) = markovFDD (P.map (X 0)) kappa n A :=
-- proof
  markov_chain_fdd P X hmeas kappa n A hA hmarkov


-- created on 2026-10-23
