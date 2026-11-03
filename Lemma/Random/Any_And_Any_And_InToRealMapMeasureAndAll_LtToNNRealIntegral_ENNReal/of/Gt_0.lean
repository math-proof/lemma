import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Polish
import Initialize.Tactic.Attr.Basic
open Classical Filter Finset MeasureTheory Metric Set Topology
open scoped ENNReal


/--
A weak neighborhood fixed by finitely many nonnegative bounded continuous test functions contains
the cell-mass fiber of a finite measurable level map. Any probability whose cell masses lie in a
small open set of frequency vectors has test-function integrals within the prescribed tolerance.
-/
@[path]
private lemma main
  [TopologicalSpace α] [PolishSpace α] [MeasurableSpace α] [BorelSpace α]
  {ν : ProbabilityMeasure α}
  {s : Finset (BoundedContinuousFunction α NNReal)}
  {ε : ℝ}
-- given
  (hε : 0 < ε) :
-- imply
  ∃ N : ℕ, ∃ φ : α → (↥s → Fin (N + 1)), Measurable φ ∧
    ∃ V : Set ((↥s → Fin (N + 1)) → ℝ), IsOpen V ∧
      (fun a => ((ν : Measure α).map φ {a}).toReal) ∈ V ∧
      ∀ ρ : ProbabilityMeasure α,
        (fun a => ((ρ : Measure α).map φ {a}).toReal) ∈ V →
        ∀ f ∈ s, dist
          (∫⁻ x, (f x : ENNReal) ∂(ρ : Measure α)).toNNReal
          (∫⁻ x, (f x : ENNReal) ∂(ν : Measure α)).toNNReal < ε :=
-- proof
by
  if hs : s.Nonempty then
    let M : ℝ := ∑ g ∈ s, dist g (BoundedContinuousFunction.const α 0)
    have hMnonneg : 0 ≤ M := Finset.sum_nonneg fun _ _ => dist_nonneg
    have hM1 : 0 < M + 1 := by linarith
    obtain ⟨n, hn⟩ := exists_nat_gt (4 / ε)
    have hn0 : (0 : ℝ) < n := lt_trans (div_pos (by norm_num : (0 : ℝ) < 4) hε) hn
    have hnε : (1 : ℝ) / n < ε / 4 := by
      rw [div_lt_iff₀ hn0]
      have h4 : (4 : ℝ) < (n : ℝ) * ε := by
        rwa [div_lt_iff₀ hε] at hn
      linarith
    let N : ℕ := ⌊(n : ℝ) * M⌋.toNat
    have hlt : ∀ x, ∀ f : ↥s, (⌊(n : ℝ) * (f.1 x : ℝ)⌋).toNat < N + 1 := by
      intro x f
      have hM : dist f.1 (BoundedContinuousFunction.const α 0) ≤ M :=
        Finset.single_le_sum (f := fun g => dist g (BoundedContinuousFunction.const α 0))
          (fun _ _ => dist_nonneg) f.2
      have hx : (f.1 x : ℝ) ≤ dist f.1 (BoundedContinuousFunction.const α 0) := by
        have hdist := BoundedContinuousFunction.dist_coe_le_dist
          (f := f.1) (g := BoundedContinuousFunction.const α 0) x
        have hzero : dist (f.1 x) (0 : NNReal) =
            dist ((f.1 x : NNReal) : ℝ) ((0 : NNReal) : ℝ) := rfl
        simpa [hzero, Real.dist_0_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)] using hdist
      have hmul : (n : ℝ) * (f.1 x : ℝ) ≤ (n : ℝ) * M :=
        mul_le_mul_of_nonneg_left (hx.trans hM) hn0.le
      refine Nat.lt_succ_of_le ?_
      simpa [N] using Int.toNat_le_toNat (Int.floor_le_floor hmul)
    let β := ↥s → Fin (N + 1)
    let φ : α → β := fun x f => ⟨(⌊(n : ℝ) * (f.1 x : ℝ)⌋).toNat, hlt x f⟩
    have hφ : Measurable φ := by
      rw [measurable_pi_iff]
      intro f
      have hfloor : Measurable fun x => ⌊(n : ℝ) * (f.1 x : ℝ)⌋ :=
        ((NNReal.continuous_coe.measurable.comp f.1.continuous.measurable).const_mul (n : ℝ)).floor
      have hnat : Measurable fun x => (⌊(n : ℝ) * (f.1 x : ℝ)⌋).toNat :=
        (measurable_of_countable Int.toNat).comp hfloor
      let toFin : ℕ → Fin (N + 1) := fun k => if h : k < N + 1 then ⟨k, h⟩ else ⟨0, Nat.succ_pos _⟩
      have htoFin : Measurable toFin := measurable_of_countable toFin
      convert htoFin.comp hnat using 1
      ext x
      simp only [φ, toFin, Function.comp_apply, dite_eq_left (hlt x f)]
    let mass : ProbabilityMeasure α → β → ℝ :=
      fun ρ a => ((ρ : Measure α).map φ {a}).toReal
    let cardβ : ℝ := Fintype.card β
    have hcard : (0 : ℝ) < cardβ + 1 := by positivity
    let δ : ℝ := ε / (2 * (cardβ + 1) * (M + 1))
    have hδ : 0 < δ := by positivity
    let V : Set (β → ℝ) := {p | ∀ a, |p a - mass ν a| < δ}
    have hV : IsOpen V := by
      have heq : V = ⋂ a : β, (fun p : β → ℝ => p a) ⁻¹' Ioo (mass ν a - δ) (mass ν a + δ) := by
        ext p
        simp only [V, Set.mem_iInter, Set.mem_preimage, Set.mem_Ioo]
        constructor
        ·
          intro h a
          have habs := abs_lt.mp (h a)
          exact ⟨by linarith [habs.1], by linarith [habs.2]⟩
        ·
          intro h a
          exact abs_lt.mpr ⟨by linarith [(h a).1], by linarith [(h a).2]⟩
      rw [heq]
      refine isOpen_iInter_of_finite fun a => isOpen_Ioo.preimage (continuous_apply a)
    have hνV : mass ν ∈ V := by
      intro a
      simpa using hδ
    refine ⟨N, φ, hφ, V, hV, hνV, ?_⟩
    intro ρ hρ f hf
    have hcoe : ∀ x, (f x : ENNReal) = ENNReal.ofReal (f x : ℝ) :=
      fun x => (ENNReal.ofReal_coe_nnreal (p := f x)).symm
    have hint : ∀ (ρ : ProbabilityMeasure α),
        ((∫⁻ x, (f x : ENNReal) ∂(ρ : Measure α)).toNNReal : ℝ) =
          ∫ x, (f x : ℝ) ∂(ρ : Measure α) := by
      intro ρ
      rw [show ((∫⁻ x, (f x : ENNReal) ∂(ρ : Measure α)).toNNReal : ℝ) =
          (∫⁻ x, (f x : ENNReal) ∂(ρ : Measure α)).toReal from rfl]
      rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => NNReal.coe_nonneg (f x))]
      · rw [show (fun x => (f x : ENNReal)) = fun x => ENNReal.ofReal (f x : ℝ) from funext hcoe]
      · exact (NNReal.continuous_coe.measurable.comp f.continuous.measurable).aestronglyMeasurable
    let approx : α → ℝ := fun x => ((⌊(n : ℝ) * (f x : ℝ)⌋).toNat : ℝ) / n
    have hgap : ∀ x, 0 ≤ (f x : ℝ) - approx x ∧ (f x : ℝ) - approx x ≤ 1 / n := by
      intro x
      have hy : (0 : ℝ) ≤ (n : ℝ) * (f x : ℝ) := mul_nonneg hn0.le (NNReal.coe_nonneg _)
      have hfloor0 : 0 ≤ ⌊(n : ℝ) * (f x : ℝ)⌋ := Int.floor_nonneg.mpr hy
      have hcast : ((⌊(n : ℝ) * (f x : ℝ)⌋).toNat : ℝ) = (⌊(n : ℝ) * (f x : ℝ)⌋ : ℝ) := by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg hfloor0]
      constructor
      · simp only [approx]
        rw [hcast, sub_nonneg, div_le_iff₀ hn0]
        have hfl := Int.floor_le ((n : ℝ) * (f x : ℝ))
        linarith
      · simp only [approx]
        rw [hcast, sub_le_iff_le_add, ← add_div, le_div_iff₀ hn0]
        have hlt1 : (n : ℝ) * (f x : ℝ) < (⌊(n : ℝ) * (f x : ℝ)⌋ : ℝ) + 1 :=
          Int.lt_floor_add_one _
        linarith
    have happrox_int : ∀ (ρ : ProbabilityMeasure α),
        |∫ x, (f x : ℝ) ∂(ρ : Measure α) - ∫ x, approx x ∂(ρ : Measure α)| ≤ 1 / n := by
      intro ρ
      have hbound : ∀ x, ‖(f x : ℝ)‖ ≤ dist f (BoundedContinuousFunction.const α 0) := by
        intro x
        have hdist := BoundedContinuousFunction.dist_coe_le_dist
          (f := f) (g := BoundedContinuousFunction.const α 0) x
        have hzero : dist (f x) (0 : NNReal) =
            dist ((f x : NNReal) : ℝ) ((0 : NNReal) : ℝ) := rfl
        have hx : (f x : ℝ) ≤ dist f (BoundedContinuousFunction.const α 0) := by
          simpa [hzero, Real.dist_0_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)] using hdist
        simpa using hx
      have hf_int : Integrable (fun x => (f x : ℝ)) (ρ : Measure α) :=
        Integrable.of_bound
          ((NNReal.continuous_coe.measurable.comp f.continuous.measurable).aestronglyMeasurable)
          (dist f (BoundedContinuousFunction.const α 0)) (ae_of_all _ hbound)
      have ha_meas : AEStronglyMeasurable approx (ρ : Measure α) := by
        exact ((continuous_of_discreteTopology.measurable.comp
          ((measurable_of_countable Int.toNat).comp
            ((NNReal.continuous_coe.measurable.comp f.continuous.measurable).const_mul
              (n : ℝ)).floor)).div_const (n : ℝ)).aestronglyMeasurable
      have ha_int : Integrable approx (ρ : Measure α) := by
        refine Integrable.of_bound ha_meas (dist f (BoundedContinuousFunction.const α 0) + 1 / n)
          (ae_of_all _ fun x => ?_)
        have hgapx := hgap x
        have habs : |approx x| ≤ dist f (BoundedContinuousFunction.const α 0) + 1 / n := by
          have hax : approx x ≤ (f x : ℝ) := by linarith [hgapx.1]
          have hnn : 0 ≤ approx x := by
            simp only [approx]
            positivity
          rw [abs_of_nonneg hnn]
          have hfpos : 0 ≤ (f x : ℝ) := NNReal.coe_nonneg _
          have hbx := hbound x
          rw [Real.norm_of_nonneg hfpos] at hbx
          linarith [hbx, hax]
        simpa using habs
      have hsub := integral_sub hf_int ha_int
      have hle : ∫ x, (f x : ℝ) - approx x ∂(ρ : Measure α) ≤ ∫ x, (1 : ℝ) / n ∂(ρ : Measure α) := by
        refine integral_mono (hf_int.sub ha_int) (integrable_const _) fun x => (hgap x).2
      have heqconst : ∫ x, (1 : ℝ) / n ∂(ρ : Measure α) = 1 / n := by
        simp [integral_const, probReal_univ]
      have hnonneg : 0 ≤ ∫ x, (f x : ℝ) - approx x ∂(ρ : Measure α) :=
        integral_nonneg fun x => (hgap x).1
      rw [← hsub, abs_of_nonneg hnonneg]
      exact hle.trans (le_of_eq heqconst)
    let fs : ↥s := ⟨f, hf⟩
    let c : β → ℝ := fun a => ((a fs).1 : ℝ) / n
    have happrox_eq : ∀ x, approx x = c (φ x) := by
      intro x
      rfl
    have hNle : (N : ℝ) ≤ (n : ℝ) * M := by
      have hfloor0 : 0 ≤ ⌊(n : ℝ) * M⌋ := Int.floor_nonneg.mpr (mul_nonneg hn0.le hMnonneg)
      have hcastN : (N : ℝ) = (⌊(n : ℝ) * M⌋ : ℝ) := by
        simp only [N]
        rw [← Int.cast_natCast, Int.toNat_of_nonneg hfloor0]
      linarith [Int.floor_le ((n : ℝ) * M)]
    have hc_bound : ∀ a, |c a| ≤ M + 1 := by
      intro a
      have hnn : 0 ≤ c a := by
        simp only [c]
        positivity
      rw [abs_of_nonneg hnn]
      have hval : ((a fs).1 : ℝ) ≤ N := by
        exact_mod_cast Nat.lt_succ_iff.mp (a fs).2
      have hdiv : ((a fs).1 : ℝ) / n ≤ (N : ℝ) / n :=
        div_le_div_of_nonneg_right hval hn0.le
      have hNm : (N : ℝ) / n ≤ M := by
        rw [div_le_iff₀ hn0]
        linarith [hNle]
      simp only [c]
      linarith
    have hcell : ∀ (σ : ProbabilityMeasure α),
        ∫ x, approx x ∂(σ : Measure α) = ∑ a, mass σ a * c a := by
      intro σ
      have hc_meas : Measurable c := measurable_of_countable c
      have hmap := integral_map (μ := (σ : Measure α)) hφ.aemeasurable
        hc_meas.aestronglyMeasurable
      have hcomp : (fun x => c (φ x)) = approx := by
        ext x
        exact (happrox_eq x).symm
      rw [← hcomp, ← hmap]
      have hintc : Integrable c ((σ : Measure α).map φ) :=
        Integrable.of_bound hc_meas.aestronglyMeasurable (M + 1) (ae_of_all _ fun a => by
          simpa using hc_bound a)
      rw [integral_countable hintc, tsum_fintype]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [smul_eq_mul, measureReal_def]
    have hdiff : |∫ x, approx x ∂(ρ : Measure α) - ∫ x, approx x ∂(ν : Measure α)| < ε / 2 := by
      rw [hcell ρ, hcell ν, ← Finset.sum_sub_distrib]
      have halg : ∑ a, (mass ρ a * c a - mass ν a * c a) =
          ∑ a, c a * (mass ρ a - mass ν a) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        ring
      rw [halg]
      have hterm : ∀ a ∈ Finset.univ, |c a * (mass ρ a - mass ν a)| < (M + 1) * δ := by
        intro a _
        rw [abs_mul]
        exact (mul_le_mul_of_nonneg_right (hc_bound a) (abs_nonneg _)).trans_lt
          (mul_lt_mul_of_pos_left (hρ a) hM1)
      have hβ : Nonempty β := inferInstance
      obtain ⟨a0⟩ := hβ
      have hsumlt := Finset.sum_lt_sum (fun a ha => (hterm a ha).le)
        ⟨a0, Finset.mem_univ _, hterm a0 (Finset.mem_univ a0)⟩
      have hconst : ∑ a : β, (M + 1) * δ = cardβ * ((M + 1) * δ) := by
        simp [Finset.sum_const, Finset.card_univ, cardβ, nsmul_eq_mul]
      have hbudget : cardβ * ((M + 1) * δ) < ε / 2 := by
        have hδdef : δ = ε / (2 * (cardβ + 1) * (M + 1)) := rfl
        rw [hδdef]
        have hden : 0 < 2 * (cardβ + 1) * (M + 1) := by positivity
        have hmul : cardβ * ((M + 1) * (ε / (2 * (cardβ + 1) * (M + 1)))) =
            cardβ * (M + 1) * ε / (2 * (cardβ + 1) * (M + 1)) := by
          ring
        rw [hmul, div_lt_iff₀ hden]
        nlinarith [hcard, hM1]
      calc
        _ ≤ ∑ a, |c a * (mass ρ a - mass ν a)| := Finset.abs_sum_le_sum_abs _ _
        _ < ∑ a, (M + 1) * δ := hsumlt
        _ < ε / 2 := by
          rw [hconst]
          exact hbudget
    have hstep1 := abs_sub_le (∫ x, (f x : ℝ) ∂(ρ : Measure α))
      (∫ x, approx x ∂(ρ : Measure α)) (∫ x, (f x : ℝ) ∂(ν : Measure α))
    have hstep2 := abs_sub_le (∫ x, approx x ∂(ρ : Measure α))
      (∫ x, approx x ∂(ν : Measure α)) (∫ x, (f x : ℝ) ∂(ν : Measure α))
    have htri : |∫ x, (f x : ℝ) ∂(ρ : Measure α) - ∫ x, (f x : ℝ) ∂(ν : Measure α)| ≤
        |∫ x, (f x : ℝ) ∂(ρ : Measure α) - ∫ x, approx x ∂(ρ : Measure α)| +
        |∫ x, approx x ∂(ρ : Measure α) - ∫ x, approx x ∂(ν : Measure α)| +
        |∫ x, approx x ∂(ν : Measure α) - ∫ x, (f x : ℝ) ∂(ν : Measure α)| := by
      linarith
    have hpair : |∫ x, (f x : ℝ) ∂(ρ : Measure α) - ∫ x, approx x ∂(ρ : Measure α)| +
        |∫ x, approx x ∂(ν : Measure α) - ∫ x, (f x : ℝ) ∂(ν : Measure α)| < ε / 2 := by
      have hp := happrox_int ρ
      have hq := happrox_int ν
      rw [abs_sub_comm] at hq
      linarith
    have hclose : |∫ x, (f x : ℝ) ∂(ρ : Measure α) - ∫ x, (f x : ℝ) ∂(ν : Measure α)| < ε := by
      linarith
    have hdist : dist (∫⁻ x, (f x : ENNReal) ∂(ρ : Measure α)).toNNReal (∫⁻ x, (f x : ENNReal) ∂(ν : Measure α)).toNNReal = |∫ x, (f x : ℝ) ∂(ρ : Measure α) - ∫ x, (f x : ℝ) ∂(ν : Measure α)| := by
      have hρi := hint ρ
      have hνi := hint ν
      rw [show dist ((∫⁻ x, (f x : ENNReal) ∂(ρ : Measure α)).toNNReal)
            ((∫⁻ x, (f x : ENNReal) ∂(ν : Measure α)).toNNReal) =
          dist (((∫⁻ x, (f x : ENNReal) ∂(ρ : Measure α)).toNNReal : ℝ))
            (((∫⁻ x, (f x : ENNReal) ∂(ν : Measure α)).toNNReal : ℝ)) from rfl]
      rw [hρi, hνi, Real.dist_eq]
    linarith
  else
    have hempty : IsEmpty ↥s := ⟨fun f => hs ⟨f.1, f.2⟩⟩
    let φ : α → (↥s → Fin 1) := fun _ f => hempty.elim f
    refine ⟨0, φ, measurable_const, univ, isOpen_univ, mem_univ _, ?_⟩
    intro ρ hρ f hf
    exact (hs ⟨f, hf⟩).elim


-- created on 2026-11-02
