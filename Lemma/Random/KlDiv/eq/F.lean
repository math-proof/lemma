import Lemma.Random.Any_And_Any_All_LeAbsAndLe_Integral_Sub_Log_Integral_Exp.of.EqKlDiv_Top
import Lemma.Random.Any_ContinuousAndAny_All_LeAbsAndLeSubToRealIntegral_Sub_Log.of.Lt0
import Lemma.Random.Integral_Sub_Log_Integral_Exp.le.ToRealKlDiv.of.Any_All_LeAbs.Continuous.Integrable_Llr
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Order.Monotone
import Initialize.Tactic.Attr.Basic
open BoundedContinuousFunction ENNReal InformationTheory MeasureTheory Random Set Real


private lemma variational [TopologicalSpace α] [PolishSpace α] [MeasurableSpace α] [BorelSpace α] {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : klDiv ν μ = ⨆ f : BoundedContinuousFunction α ℝ, ENNReal.ofReal (∫ x, f x ∂ν - log (∫ x, exp (f x) ∂μ)) := by
  let expr : (BoundedContinuousFunction α ℝ) → ℝ := fun f => ∫ x, f x ∂ν - log (∫ x, exp (f x) ∂μ)
  apply le_antisymm
  ·
    if htop : klDiv ν μ = ⊤ then
      rw [htop]
      refine (iSup_eq_top.mpr fun b hb => ?_).ge
      obtain ⟨g, hg, ⟨C, hC⟩, hge⟩ :=
        Any_And_Any_All_LeAbsAndLe_Integral_Sub_Log_Integral_Exp.of.EqKlDiv_Top htop (b.toReal + 1)
      let φ := ofNormedAddCommGroup g hg C fun x => by simpa [Real.norm_eq_abs] using hC x
      have hcoe : (φ : α → ℝ) = g := coe_ofNormedAddCommGroup g hg C _
      refine ⟨φ, ?_⟩
      calc
        _ = ENNReal.ofReal b.toReal := (ofReal_toReal hb.ne).symm
        _ < ENNReal.ofReal (b.toReal + 1) :=
          (ofReal_lt_ofReal_iff (add_pos_of_nonneg_of_pos toReal_nonneg one_pos)).mpr
            (lt_add_of_pos_right _ one_pos)
        _ ≤ ENNReal.ofReal (expr φ) :=
          ofReal_le_ofReal (by simpa [expr, hcoe] using hge)
    else
      have hpair := klDiv_ne_top_iff.mp htop
      let r := (klDiv ν μ).toReal
      have hbdd : BddAbove (range fun n : ℕ => r - ((n : ℝ) + 1)⁻¹) := by
        refine ⟨r, ?_⟩
        intro y hy
        obtain ⟨n, rfl⟩ := hy
        exact sub_le_self r (inv_nonneg.mpr (add_nonneg (Nat.cast_nonneg n) zero_le_one))
      have hsup : ⨆ n : ℕ, r - ((n : ℝ) + 1)⁻¹ = r := by
        apply le_antisymm
        · exact ciSup_le fun n => sub_le_self r (inv_nonneg.mpr (add_nonneg (Nat.cast_nonneg _) zero_le_one))
        ·
          refine le_of_forall_pos_le_add fun ε hε => ?_
          obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
          have hle : r - ((n : ℝ) + 1)⁻¹ ≤ ⨆ k : ℕ, r - ((k : ℝ) + 1)⁻¹ := le_ciSup hbdd n
          have hn' : ((n : ℝ) + 1)⁻¹ < ε := by simpa [one_div] using hn
          linarith [hle, hn']
      have hof : ENNReal.ofReal r = ⨆ n : ℕ, ENNReal.ofReal (r - ((n : ℝ) + 1)⁻¹) := by
        simpa [hsup] using
          ofReal_mono.map_ciSup_of_continuousAt
            (g := fun n : ℕ => r - ((n : ℝ) + 1)⁻¹) continuous_ofReal.continuousAt hbdd
      have hterm : ∀ n : ℕ, ENNReal.ofReal (r - ((n : ℝ) + 1)⁻¹) ≤ ⨆ f, ENNReal.ofReal (expr f) := by
        intro n
        have hε : 0 < ((n : ℝ) + 1)⁻¹ :=
          inv_pos.mpr (add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) one_pos)
        obtain ⟨g, hg, ⟨C, hC⟩, hge⟩ :=
          Any_ContinuousAndAny_All_LeAbsAndLeSubToRealIntegral_Sub_Log.of.Lt0 hpair.1 hpair.2 hε
        let φ := ofNormedAddCommGroup g hg C fun x => by simpa [Real.norm_eq_abs] using hC x
        have hcoe : (φ : α → ℝ) = g := coe_ofNormedAddCommGroup g hg C _
        have hge' : r - ((n : ℝ) + 1)⁻¹ ≤ expr φ := by
          simpa [expr, hcoe] using hge
        refine (ofReal_le_ofReal hge').trans ?_
        exact le_iSup (fun f => ENNReal.ofReal (expr f)) φ
      have hreal : ENNReal.ofReal r ≤ ⨆ f, ENNReal.ofReal (expr f) :=
        (le_of_eq hof).trans (iSup_le hterm)
      simpa [r, ofReal_toReal htop] using hreal
  ·
    refine iSup_le fun f => ?_
    if htop : klDiv ν μ = ⊤ then
      simp [htop]
    else
      have hpair := klDiv_ne_top_iff.mp htop
      have hle : expr f ≤ (klDiv ν μ).toReal :=
        Integral_Sub_Log_Integral_Exp.le.ToRealKlDiv.of.Any_All_LeAbs.Continuous.Integrable_Llr
          hpair.1 hpair.2 (map_continuous f)
          ⟨‖f‖, fun x => by simpa [Real.norm_eq_abs] using f.norm_coe_le_norm x⟩
      calc
        _ ≤ ENNReal.ofReal ((klDiv ν μ).toReal) := ofReal_le_ofReal hle
        _ = klDiv ν μ := ofReal_toReal htop

/--
On a Polish space the Kullback–Leibler divergence is the supremum of the Donsker–Varadhan expression
over bounded continuous test functions. The supremum is an extended real, so it stays infinite when
the divergence is.
-/
@[path]
private lemma main
  [TopologicalSpace α] [PolishSpace α] [MeasurableSpace α] [BorelSpace α]
  {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
-- imply
  klDiv ν μ = ⨆ f : BoundedContinuousFunction α ℝ, ENNReal.ofReal (∫ x, f x ∂ν - log (∫ x, exp (f x) ∂μ)) :=
-- proof
variational


-- created on 2026-11-02
