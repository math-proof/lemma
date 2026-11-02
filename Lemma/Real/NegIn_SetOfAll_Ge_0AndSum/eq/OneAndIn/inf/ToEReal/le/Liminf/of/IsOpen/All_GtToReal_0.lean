import Mathlib.Data.EReal.Operations
import Mathlib.Order.CompleteLattice.Basic
import Lemma.Real.NegToEReal.le.Liminf.of.In.IsOpen.All_GtToReal_0.EqSum_1.All_Ge_0
import Initialize.Tactic.Attr.Basic
open Filter MeasureTheory Real


private lemma neg_iInf {ι : Sort*} (f : ι → EReal) :
  -(⨅ i, f i) = ⨆ i, -f i := by
  apply le_antisymm
  ·
    rw [EReal.neg_le]
    refine le_iInf ?_
    intro i
    rw [EReal.neg_le]
    exact le_iSup (fun j => -f j) i
  ·
    refine iSup_le ?_
    intro i
    rw [EReal.neg_le_neg_iff]
    exact iInf_le f i

private lemma neg_iInf₂ {ι : Sort*} {κ : ι → Sort*} (f : ∀ i, κ i → EReal) :
  -(⨅ i, ⨅ j, f i j) = ⨆ i, ⨆ j, -f i j := by
  simp_rw [neg_iInf]

private lemma liminf_inf [Fintype α] [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α] {μ : PMF α} {U : Set (α → ℝ)} (hμ : ∀ a, 0 < (μ a).toReal) (hU : IsOpen U) :
  -(⨅ ν ∈ {ν : α → ℝ | (∀ a, 0 ≤ ν a) ∧ ∑ a, ν a = 1 ∧ ν ∈ U}, toEReal (∑ a, ν a * log (ν a / (μ a).toReal))) ≤
    liminf (fun n : ℕ => toEReal ((n : ℝ)⁻¹ * log (((Measure.pi fun _ : Fin n => μ.toMeasure) {ω : Fin n → α | (fun a => (countVec ω a : ℝ) / n) ∈ U}).toReal))) atTop := by
  rw [neg_iInf₂]
  refine iSup₂_le ?_
  intro ν hν
  obtain ⟨hge, hsum, hmem⟩ := hν
  exact NegToEReal.le.Liminf.of.In.IsOpen.All_GtToReal_0.EqSum_1.All_Ge_0 hge hsum hμ hU hmem

/--
If every reference mass is positive, the logarithmic probability that the empirical frequency lands
in an open set `U` has liminf at least the negative infimum of `KL(ν ‖ μ)` over the probability
vectors in `U`.
-/
@[path]
private lemma main
  [Fintype α] [DecidableEq α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
  {μ : PMF α} {U : Set (α → ℝ)}
-- given
  (hμ : ∀ a, 0 < (μ a).toReal)
  (hU : IsOpen U) :
-- imply
  -(⨅ ν ∈ {ν : α → ℝ | (∀ a, 0 ≤ ν a) ∧ ∑ a, ν a = 1 ∧ ν ∈ U}, toEReal (∑ a, ν a * log (ν a / (μ a).toReal))) ≤
    liminf (fun n : ℕ => toEReal ((n : ℝ)⁻¹ * log (((Measure.pi fun _ : Fin n => μ.toMeasure) {ω : Fin n → α | (fun a => (countVec ω a : ℝ) / n) ∈ U}).toReal))) atTop :=
-- proof
  liminf_inf hμ hU


-- created on 2026-11-02
