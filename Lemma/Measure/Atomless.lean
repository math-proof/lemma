import Mathlib
import sympy.Basic
import Theorem.MeasureTheory.Measure.Atomless.Part3
open MeasureTheory Set Filter Topology
open MeasureTheory


namespace MeasureTheory

/--
[isAtomless_restrict](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Measure/Atomless.lean)
-/
@[path]
lemma isAtomless_restrict
  [MeasurableSpace α]
  {μ : Measure α}
  {Z : Set α}
-- given
  (hZ : MeasurableSet Z)
  (hA : IsAtomless μ) :
-- imply
  IsAtomless (μ.restrict Z) := by
-- proof
  intro s hs hspos
  have hrestr : (μ.restrict Z) s = μ (s ∩ Z) := Measure.restrict_apply hs
  rw [hrestr] at hspos
  have hmeas : MeasurableSet (s ∩ Z) := hs.inter hZ
  obtain ⟨t, hts, htmeas, htpos, htlt⟩ := hA (s ∩ Z) hmeas hspos
  have htrestr : (μ.restrict Z) t = μ t := by
    rw [Measure.restrict_apply htmeas]
    have hsub : t ∩ Z = t :=
      Set.inter_eq_self_of_subset_left (fun x hx => (hts hx).2)
    rw [hsub]
  refine ⟨t, fun x hx => (hts hx).1, htmeas, htrestr.symm ▸ htpos, ?_⟩
  rwa [htrestr, hrestr]

end MeasureTheory

namespace MeasureTheory

/--
[isAtomless_exists_small_subset_real](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Measure/Atomless.lean)
-/
@[path]
subsets with a geometric bound. Consumed by Sierpinski (N3) and the bang-bang step. -/
private lemma isAtomless_exists_small_subset_real {α : Type*} [MeasurableSpace α]
  {μ : Measure α} [IsFiniteMeasure μ] (hA : IsAtomless μ)
  {s : Set α} (hs : MeasurableSet s) (hpos : 0 < μ s) (n : ℕ) :
  ∃ u, u ⊆ s ∧ MeasurableSet u ∧ 0 < μ u ∧ μ.real u ≤ μ.real s / 2 ^ n := by
  induction n with
  | zero =>
    refine ⟨s, le_rfl, hs, hpos, ?_⟩
    simp
  | succ n ih =>
    obtain ⟨u, hus, humeas, hupos, hule⟩ := ih
    obtain ⟨t, htu, htmeas, htpos, htlt⟩ := hA u humeas hupos
    have ht_ne_top : μ t ≠ ⊤ := (measure_lt_top μ t).ne
    have hu_ne_top : μ u ≠ ⊤ := (measure_lt_top μ u).ne
    have hdiff_meas : MeasurableSet (u \ t) := humeas.diff htmeas
    have hunion : t ∪ (u \ t) = u := Set.union_sdiff_cancel htu
    have hdisj : Disjoint t (u \ t) := disjoint_sdiff_self_right
    have hdiff_eq : μ.real (u \ t) = μ.real u - μ.real t :=
      measureReal_sdiff htu htmeas
    have hdiff_pos : 0 < μ.real (u \ t) := by
      rw [hdiff_eq]
      have hlt : μ.real t < μ.real u :=
        (ENNReal.toReal_lt_toReal ht_ne_top hu_ne_top).mpr htlt
      linarith
    have hdiff_ne : μ (u \ t) ≠ 0 := by
      intro h0
      have hrz : μ.real (u \ t) = 0 := by
        rw [measureReal_def, h0, ENNReal.toReal_zero]
      linarith
    have hdiff_pos_enn : 0 < μ (u \ t) := bot_lt_iff_ne_bot.mpr hdiff_ne
    have hsum : μ.real t + μ.real (u \ t) = μ.real u := by
      have hun := measureReal_union hdisj hdiff_meas (μ := μ)
      rw [hunion] at hun
      linarith
    by_cases hcase : μ.real t ≤ μ.real u / 2
    · refine ⟨t, htu.trans hus, htmeas, htpos, ?_⟩
      calc μ.real t ≤ μ.real u / 2 := hcase
        _ ≤ (μ.real s / 2 ^ n) / 2 := by linarith [hule]
        _ = μ.real s / 2 ^ (n + 1) := by ring
    · have hlt : μ.real u / 2 < μ.real t := lt_of_not_ge hcase
      have hsmall : μ.real (u \ t) ≤ μ.real u / 2 := by linarith [hsum, hlt]
      refine ⟨u \ t, (Set.sdiff_subset.trans hus), hdiff_meas, hdiff_pos_enn, ?_⟩
      calc μ.real (u \ t) ≤ μ.real u / 2 := hsmall
        _ ≤ (μ.real s / 2 ^ n) / 2 := by linarith [hule]
        _ = μ.real s / 2 ^ (n + 1) := by ring

end MeasureTheory

namespace MeasureTheory

/--
[isAtomless_exists_small_subset_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Measure/Atomless.lean)
-/
@[path]
positive real bound. -/
private lemma isAtomless_exists_small_subset_le {α : Type*} [MeasurableSpace α]
  {μ : Measure α} [IsFiniteMeasure μ] (hA : IsAtomless μ)
  {s : Set α} (hs : MeasurableSet s) (hpos : 0 < μ s)
  {ε : ℝ} (hε : 0 < ε) :
  ∃ u, u ⊆ s ∧ MeasurableSet u ∧ 0 < μ u ∧ μ.real u ≤ ε := by
  obtain ⟨n, hn⟩ :=
    pow_unbounded_of_one_lt ((μ.real s + 1) / ε) (show (1:ℝ) < 2 by norm_num)
  have h2n : (0 : ℝ) < 2 ^ n := pow_pos (by norm_num) n
  have hle : μ.real s / 2 ^ n ≤ ε := by
    have h1 := (div_lt_iff₀ hε).mp hn
    have h2 : μ.real s ≤ ε * 2 ^ n := by linarith
    exact (div_le_iff₀ h2n).mpr h2
  obtain ⟨u, hus, humeas, hupos, hu2n⟩ :=
    isAtomless_exists_small_subset_real hA hs hpos n
  exact ⟨u, hus, humeas, hupos, le_trans hu2n hle⟩

end MeasureTheory

namespace MeasureTheory

/--
[sierpinskiSeq_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Measure/Atomless.lean)
-/
@[path]
private lemma sierpinskiSeq_succ {α : Type*} [MeasurableSpace α]
  {μ : Measure α} [IsFiniteMeasure μ] {s : Set α}
  {t : ENNReal} (ht : t ≤ μ s) (n : ℕ) :
  (sierpinskiSeq ht (n + 1)).u =
    (sierpinskiSeq ht n).u ∪ sierpinskiPiece ht (sierpinskiSeq ht n) :=
  rfl

end MeasureTheory

namespace MeasureTheory

/--
[sierpinskiSeq_mono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Measure/Atomless.lean)
-/
@[path]
private lemma sierpinskiSeq_mono {α : Type*} [MeasurableSpace α]
  {μ : Measure α} [IsFiniteMeasure μ] {s : Set α}
  {t : ENNReal} (ht : t ≤ μ s) :
  Monotone (fun n => ((sierpinskiSeq ht n).u)) := by
  apply monotone_nat_of_le_succ
  intro n
  rwa [sierpinskiSeq_succ ht n]

end MeasureTheory

/--
[isAtomless_exists_subset_measure_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Measure/Atomless.lean)
-/
@[path]
private lemma isAtomless_exists_subset_measure_eq_eq
  [MeasurableSpace α]
  {μ : Measure α} [IsFiniteMeasure μ]
  {s : Set α}
  {t : ENNReal}
-- given
  (hA : IsAtomless μ)
  (hs : MeasurableSet s)
  (ht : t ≤ μ s) :
-- imply
  ∃ u, u ⊆ s ∧ MeasurableSet u ∧ μ u = t := by
-- proof
  apply MeasureTheory.isAtomless_exists_subset_measure_eq hA hs ht


-- created on 2026-10-20
-- updated on 2026-10-23
