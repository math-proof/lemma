import Mathlib
import sympy.Basic
open Set Filter Topology ENNReal
open ENNReal
open MeasureTheory

/--
[measurableSpace_isSetAlgebra](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToFunctionalAnalysis/code/MeasureTheory.lean)
-/
@[path]
lemma measurableSpace_isSetAlgebra
  {α : Type*}
  [m : MeasurableSpace α] :
-- imply
  IsSetAlgebra {s : Set α | MeasurableSet s} where
    empty_mem := MeasurableSet.empty
    compl_mem := fun {s} (hs : MeasurableSet s) => hs.compl
    union_mem := fun {s t} (hs : MeasurableSet s) (ht : MeasurableSet t) => hs.union ht

/--
[sigmaAlgebra_finite_union_mem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToFunctionalAnalysis/code/MeasureTheory.lean)
-/
@[path]
lemma sigmaAlgebra_finite_union_mem
  [MeasurableSpace α]
  {f : ι → Set α}
  {S : Finset ι}
-- given
  (hf : ∀ i ∈ S, MeasurableSet (f i)) :
-- imply
  MeasurableSet (⋃ i ∈ S, f i) :=
-- proof
  S.measurableSet_biUnion hf

/--
[exists_disjoint_seq_with_same_union](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToFunctionalAnalysis/code/MeasureTheory.lean)
-/
@[path]
lemma exists_disjoint_seq_with_same_union
  [MeasurableSpace α]
  {E : ℕ → Set α}
-- given
  (hE : ∀ n, MeasurableSet (E n)) :
-- imply
  ∃ F : ℕ → Set α, (∀ n, MeasurableSet (F n)) ∧ Pairwise (Function.onFun Disjoint F) ∧ (⋃ n, F n) = (⋃ n, E n) :=
-- proof
  ⟨disjointed E,
    fun n => MeasurableSet.disjointed hE n,
    disjoint_disjointed E,
    iUnion_disjointed⟩

/--
[lebesgue_measurableSet_sigmaAlgebra](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToFunctionalAnalysis/code/MeasureTheory.lean)
-/
@[path]
lemma lebesgue_measurableSet_sigmaAlgebra :
-- imply
  (NullMeasurableSet (∅ : Set ℝ) volume) ∧ (∀ s : Set ℝ, NullMeasurableSet s volume → NullMeasurableSet sᶜ volume) ∧ (∀ f : ℕ → Set ℝ, (∀ n, NullMeasurableSet (f n) volume) → NullMeasurableSet (⋃ n, f n) volume) :=
-- proof
  ⟨nullMeasurableSet_empty, fun _ hs => hs.compl, fun _ hf => .iUnion hf⟩

/--
[continuity_measure_increasing](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToFunctionalAnalysis/code/MeasureTheory.lean)
-/
@[path]
lemma continuity_measure_increasing
  [MeasurableSpace α]
  {μ : Measure α}
  {E : ℕ → Set α}
-- given
  (hE : Monotone E) :
-- imply
  Tendsto (fun n => μ (E n)) atTop (𝓝 (μ (⋃ n, E n))) :=
-- proof
  tendsto_measure_iUnion_atTop hE

/--
[measurable_of_pointwise_limit](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToFunctionalAnalysis/code/MeasureTheory.lean)
-/
@[path]
lemma measurable_of_pointwise_limit
  [MeasurableSpace α]
  {f : ℕ → α → EReal}
  {g : α → EReal}
-- given
  (hf : ∀ n, Measurable (f n))
  (hlim : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
-- imply
  Measurable g := by
-- proof
  have : TopologicalSpace.PseudoMetrizableSpace EReal :=
    TopologicalSpace.PseudoMetrizableSpace.of_regularSpace_secondCountableTopology EReal
  exact measurable_of_tendsto_metrizable hf (tendsto_pi_nhds.mpr hlim)

/--
[simpleFunc_closed_scalar_add_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToFunctionalAnalysis/code/MeasureTheory.lean)
-/
@[path]
lemma simpleFunc_closed_scalar_add_mul
  [MeasurableSpace α]
  [AddCommMonoid β]
  [Mul β]
  [SMul K β] :
-- imply
  (∀ (c : K) (f : SimpleFunc α β), ∃ g : SimpleFunc α β, ⇑g = c • ⇑f) ∧ (∀ (f g : SimpleFunc α β), ∃ h : SimpleFunc α β, ⇑h = ⇑f + ⇑g) ∧ (∀ (f g : SimpleFunc α β), ∃ h : SimpleFunc α β, ⇑h = ⇑f * ⇑g) :=
-- proof
  ⟨fun c f => ⟨c • f, rfl⟩, fun f g => ⟨f + g, rfl⟩, fun f g => ⟨f * g, rfl⟩⟩

namespace MeasureTheory.SimpleFunc

open MeasureTheory.SimpleFunc

/--
[exists_monotone_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToFunctionalAnalysis/code/MeasureTheory.lean)
-/
@[path]
lemma exists_monotone_tendsto
  [MeasurableSpace α]
  {f : α → ENNReal}
-- given
  (hf : Measurable f) :
-- imply
  ∃ φ : ℕ → SimpleFunc α ENNReal, ((∀ n a, φ n a ≤ f a) ∧ (Monotone fun n => (φ n : α → ENNReal))) ∧ (∀ a, Tendsto (fun n => φ n a) atTop (𝓝 (f a))) ∧ (∀ B : ENNReal, B ≠ ⊤ → ∀ ε : ENNReal, ε ≠ 0 → ∃ N : ℕ, ∀ n ≥ N, ∀ a, f a ≤ B → f a - φ n a < ε) := by
-- proof
  refine ⟨eapprox f, ⟨?_, ?_⟩, ?_, ?_⟩
  ·
    exact fun n a => (iSup_eapprox_apply hf a ▸ le_iSup (fun n => (eapprox f n) a) n)
  ·
    exact fun _ _ h a => monotone_eapprox f h a
  ·
    exact fun a => tendsto_eapprox hf a
  ·
    intro B hB ε hε
    by_cases hε_top : ε = ⊤
    · exact ⟨0, fun n _ a ha => by
      rw [hε_top]
      exact tsub_le_self.trans_lt (lt_top_iff_ne_top.mpr (ne_top_of_le_ne_top hB ha))⟩
    have hε_pos : (0 : ENNReal) < ε := pos_iff_ne_zero.mpr hε
    have hB_lt : B < ⊤ := lt_top_iff_ne_top.mpr hB
    obtain ⟨r, hr_pos, hrε⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hε_pos
    have hr_real_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast ENNReal.coe_pos.mp hr_pos
    obtain ⟨q, hq_pos_real, hqr⟩ := exists_rat_btwn hr_real_pos
    have hq_pos : (0 : ℝ) < (q : ℝ) := by linarith
    have h_ofReal_lt_r : ENNReal.ofReal (q : ℝ) < (r : ENNReal) := by
      rw [← ENNReal.ofReal_coe_nnreal]
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (le_of_lt hq_pos)).mpr hqr
    have hq_lt_ε : ENNReal.ofReal (q : ℝ) < ε := lt_trans h_ofReal_lt_r hrε
    set k := Nat.ceil (B.toReal / (q : ℝ))
    set N := 1 + (Finset.range (k + 1)).sup (fun i => Encodable.encode ((↑i : ℚ) * q))
    use N
    intro n hn a ha
    by_cases hfa_zero : f a = 0
    · simp [hfa_zero, hε_pos]
    have hfa_lt : f a < ⊤ := lt_of_le_of_lt ha hB_lt
    have hfa_ne_top : f a ≠ ⊤ := hfa_lt.ne
    set j := Nat.floor ((f a).toReal / (q : ℝ))
    have h_div_nn : (0 : ℝ) ≤ (f a).toReal / (q : ℝ) :=
      div_nonneg ENNReal.toReal_nonneg (le_of_lt hq_pos)
    have h_j_le : (↑j : ℝ) * (q : ℝ) ≤ (f a).toReal := by
      nlinarith [Nat.floor_le h_div_nn, div_mul_cancel₀ (f a).toReal (ne_of_gt hq_pos)]
    have h_diff_lt : (f a).toReal - ↑j * (q : ℝ) < (q : ℝ) := by
      nlinarith [Nat.lt_floor_add_one ((f a).toReal / (q : ℝ)),
        div_mul_cancel₀ (f a).toReal (ne_of_gt hq_pos)]
    have hj_le_k : j ≤ k :=
      (Nat.floor_le_ceil _).trans (Nat.ceil_le_ceil
        (div_le_div_of_nonneg_right ((ENNReal.toReal_le_toReal hfa_ne_top hB).mpr ha)
          (le_of_lt hq_pos)))
    have h_encode_lt : Encodable.encode ((↑j : ℚ) * q) < N := by
      have hmem : j ∈ Finset.range (k + 1) := Finset.mem_range.mpr (by omega)
      have h : Encodable.encode ((↑j : ℚ) * q) ≤
        (Finset.range (k + 1)).sup (fun i => Encodable.encode ((↑i : ℚ) * q)) :=
        Finset.le_sup_of_le hmem le_rfl
      omega
    have h_embed_val : ennrealRatEmbed (Encodable.encode ((↑j : ℚ) * q)) =
      ENNReal.ofReal (↑j * (q : ℝ)) := by
      rw [ennrealRatEmbed_encode]; simp [ENNReal.ofReal, Rat.cast_mul, Rat.cast_natCast]
    have h_embed_le : ennrealRatEmbed (Encodable.encode ((↑j : ℚ) * q)) ≤ f a := by
      rw [h_embed_val, ENNReal.ofReal_le_iff_le_toReal hfa_ne_top]; exact_mod_cast h_j_le
    have h_eapprox_ge : ENNReal.ofReal (↑j * (q : ℝ)) ≤ eapprox f n a := by
      rw [← h_embed_val]
      have h_step : ennrealRatEmbed (Encodable.encode ((↑j : ℚ) * q)) ≤
        eapprox f (Encodable.encode ((↑j : ℚ) * q) + 1) a := by
        have h := approx_apply a hf (i := ennrealRatEmbed)
          (n := Encodable.encode ((↑j : ℚ) * q) + 1)
        change ennrealRatEmbed _ ≤ (approx ennrealRatEmbed f _) a; rw [h]
        refine le_trans ?_ (Finset.le_sup (Finset.mem_range.mpr (Nat.lt_succ_self _)))
        simp [h_embed_le]
      exact h_step.trans (monotone_eapprox f (by omega) a)
    calc f a - eapprox f n a
      ≤ f a - ENNReal.ofReal (↑j * (q : ℝ)) := tsub_le_tsub_left h_eapprox_ge _
      _ < ENNReal.ofReal (q : ℝ) := by
        rw [← ENNReal.ofReal_toReal hfa_ne_top]
        rw [← ENNReal.ofReal_sub _ (show (0 : ℝ) ≤ ↑j * (q : ℝ) from by positivity)]
        exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by linarith)).mpr h_diff_lt
      _ < ε := hq_lt_ε
end MeasureTheory.SimpleFunc
open ENNReal

/--
[measurableSet_Ioi_real](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToFunctionalAnalysis/code/MeasureTheory.lean)
-/
@[path]
lemma measurableSet_Ioi_real
  {a : ℝ} :
-- imply
  MeasurableSet (Set.Ioi a) :=
-- proof
  measurableSet_Ioi


-- created on 2026-10-23
-- updated on 2026-10-24
