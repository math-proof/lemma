import Syntax.Probability.Probability
import Syntax.Data.List
import Notation.Fun
import Initialize.Tactic.Attr.Basic
import Lemma.Random.SinglePSpace.of.Measurable
import Lemma.Random.SinglePSpace.of.Measurable.Measurable
import Lemma.Random.Prob_Cond.eq.Div.of.SinglePSpace
import Lemma.Random.All_MeasurableGetSlice.of.All_Measurable
open MeasureTheory ProbabilityTheory Random Fun


/--
Chain rule for a process prefix given a random variable `Z`:

  \(\mathbb{P}_{\pi}(s[:n] \mid Z) = \prod_{k<n} \mathbb{P}_{\pi}(s[k] \mid s[:k], Z)\).

The identity holds almost surely, since the n = 0 case is `1` only on the support of `Z`.

This is the chain rule (2.4) of Manning and Schütze, [Foundations of Statistical Natural Language Processing](https://bcmi.sjtu.edu.cn/home/zhaohai/lessons/nlp2011/textbooks/Foundations-of-Statistical-Natural-Language-Processing.pdf#page=80).

See also [arXiv:2309.16058](https://arxiv.org/pdf/2309.16058.pdf#3).
-/
@[path, comm]
private lemma main
  [MeasurableSpace Ω]
  [CountableMeasure 𝒮] [CountableMeasure 𝒵]
  [Countable 𝒮] [MeasurableSingletonClass 𝒮]
  [Countable 𝒵] [MeasurableSingletonClass 𝒵]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {s : ℕ ⇀ Ω → 𝒮} {Z : Ω → 𝒵}
-- given
  (hs : ∀ k, Measurable s[k])
  (hZ : Measurable Z)
  (n : ℕ) :
-- imply
  have hslice : ∀ k : ℕ, Measurable (s[:k]) :=
    All_MeasurableGetSlice.of.All_Measurable hs
  have : SinglePSpace π (JointRandomSymbol (s[:n] : Ω → Fin n → 𝒮) Z) :=
    SinglePSpace.of.Measurable.Measurable (hslice n) hZ
  have : ∀ k, SinglePSpace π
    (JointRandomSymbol s[k] (JointRandomSymbol (s[:k] : Ω → Fin k → 𝒮) Z)) :=
    fun k =>
      SinglePSpace.of.Measurable.Measurable (hs k) ((hslice k).prodMk hZ)
  ℙ[π](s[:n] | Z) =ᵐ[π]
    ∏ k ∈ Finset.range n, ℙ[π](s[k] | s[:k], Z) := by
-- proof
  intro hslice _ _
  have hsnoc (k : ℕ) (ω : Ω) :
    s[:k.succ] ω = Fin.snoc (s[:k] ω) (s[k] ω) := by
    funext i
    refine Fin.lastCases ?_ ?_ i
    ·
      rw [Fin.snoc_last]
      rfl
    ·
      intro j
      rw [Fin.snoc_castSucc]
      rfl
  have hsnoc_iff (k : ℕ) (ω ω' : Ω) :
    s[:k.succ] ω' = s[:k.succ] ω ↔
      s[k] ω' = s[k] ω ∧ s[:k] ω' = s[:k] ω := by
    constructor
    ·
      intro h
      have h' := (hsnoc k ω').symm.trans (h.trans (hsnoc k ω))
      refine ⟨?_, ?_⟩
      ·
        have := congrArg (fun v => v (Fin.last k)) h'
        simpa [Fin.snoc_last] using this
      ·
        funext j
        have := congrArg (fun v => v j.castSucc) h'
        simpa [Fin.snoc_castSucc] using this
    ·
      intro ⟨hx, hpref⟩
      rw [hsnoc k ω', hx, hpref, hsnoc k ω]
  have hevent (k : ℕ) (ω : Ω) :
    s[:k.succ] ⁻¹' {s[:k.succ] ω} ∩ Z ⁻¹' {Z ω} =
      s[k] ⁻¹' {s[k] ω} ∩ s[:k] ⁻¹' {s[:k] ω} ∩ Z ⁻¹' {Z ω} := by
    ext ω'
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
      hsnoc_iff]
  have hZ_pos : ∀ᵐ ω ∂π, π (Z ⁻¹' {Z ω}) ≠ 0 := by
    rw [ae_iff]
    simp only [ne_eq, not_not]
    have hcov :
      {ω | π (Z ⁻¹' {Z ω}) = 0} =
        Z ⁻¹' {z | π (Z ⁻¹' {z}) = 0} := by
      ext ω
      simp
    rw [hcov]
    apply (measure_preimage_eq_zero_iff_of_countable
      ({z : 𝒵 | π (Z ⁻¹' {z}) = 0}.to_countable)).2
    intro z hz
    apply hz
  filter_upwards [hZ_pos] with ω hpos
  have hdiv_prefix (k : ℕ)
    (hP : SinglePSpace π (JointRandomSymbol (s[:k] : Ω → Fin k → 𝒮) Z)) :
    ℙ[π](s[:k] | Z) ω =
      π (s[:k] ⁻¹' {s[:k] ω} ∩ Z ⁻¹' {Z ω}) / π (Z ⁻¹' {Z ω}) := by
    apply Prob_Cond.eq.Div.of.SinglePSpace hP (s[:k] ω) (Z ω)
  have hdiv_step (k : ℕ)
    (hP : SinglePSpace π
      (JointRandomSymbol s[k] (JointRandomSymbol (s[:k] : Ω → Fin k → 𝒮) Z))) :
    ℙ[π](s[k] | s[:k], Z) ω =
      π (s[k] ⁻¹' {s[k] ω} ∩ s[:k] ⁻¹' {s[:k] ω} ∩ Z ⁻¹' {Z ω}) /
        π (s[:k] ⁻¹' {s[:k] ω} ∩ Z ⁻¹' {Z ω}) := by
    have h :=
      Prob_Cond.eq.Div.of.SinglePSpace
        (x := s[k]) (y := JointRandomSymbol (s[:k] : Ω → Fin k → 𝒮) Z)
        hP (s[k] ω) (s[:k] ω, Z ω)
    simp only [Measure.probCondRA, JointRandomSymbol]
    rw [show (s[k] ω, (s[:k] ω, Z ω)) = (s[k] ω, s[:k] ω, Z ω) from rfl] at h ⊢
    rw [h]
    have hnum :
      s[k] ⁻¹' {s[k] ω} ∩
        JointRandomSymbol (s[:k] : Ω → Fin k → 𝒮) Z ⁻¹' {(s[:k] ω, Z ω)} =
        s[k] ⁻¹' {s[k] ω} ∩ s[:k] ⁻¹' {s[:k] ω} ∩ Z ⁻¹' {Z ω} := by
      ext ω'
      simp [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
        JointRandomSymbol, Prod.ext_iff]
      tauto
    have hden :
      JointRandomSymbol (s[:k] : Ω → Fin k → 𝒮) Z ⁻¹' {(s[:k] ω, Z ω)} =
        s[:k] ⁻¹' {s[:k] ω} ∩ Z ⁻¹' {Z ω} := by
      ext ω'
      simp [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
        JointRandomSymbol, Prod.ext_iff]
    rw [hnum, hden]
  simp only [Finset.prod_apply]
  induction n with
  | zero =>
    rw [Finset.prod_range_zero]
    have hP0 : SinglePSpace π
      (JointRandomSymbol (s[:(0 : ℕ)] : Ω → Fin 0 → 𝒮) Z) :=
      SinglePSpace.of.Measurable.Measurable (hslice 0) hZ
    have hempty : s[:(0 : ℕ)] ⁻¹' {s[:(0 : ℕ)] ω} = Set.univ := by
      ext ω'
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
      funext i
      apply i.elim0
    rw [hdiv_prefix 0 hP0, hempty, Set.univ_inter,
      ENNReal.div_self hpos (measure_ne_top π _)]
  | succ n ih =>
    have hPn : SinglePSpace π
      (JointRandomSymbol (s[:n] : Ω → Fin n → 𝒮) Z) :=
      SinglePSpace.of.Measurable.Measurable (hslice n) hZ
    have hPn1 : SinglePSpace π
      (JointRandomSymbol (s[:n.succ] : Ω → Fin n.succ → 𝒮) Z) :=
      SinglePSpace.of.Measurable.Measurable (hslice n.succ) hZ
    have hPstep : SinglePSpace π
      (JointRandomSymbol s[n]
        (JointRandomSymbol (s[:n] : Ω → Fin n → 𝒮) Z)) :=
      SinglePSpace.of.Measurable.Measurable (hs n) ((hslice n).prodMk hZ)
    rw [Finset.prod_range_succ, ← ih]
    rw [hdiv_prefix n.succ hPn1, hdiv_prefix n hPn, hdiv_step n hPstep,
      hevent n ω]
    set A0 := Z ⁻¹' {Z ω}
    set An := s[:n] ⁻¹' {s[:n] ω} ∩ Z ⁻¹' {Z ω}
    set An1 := s[n] ⁻¹' {s[n] ω} ∩ s[:n] ⁻¹' {s[:n] ω} ∩ Z ⁻¹' {Z ω}
    if hmid : π An = 0 then
      have hsub : An1 ⊆ An := by
        intro ω' ⟨⟨_, hpref⟩, hZ'⟩
        apply And.intro hpref hZ'
      have hnum := measure_mono_null hsub hmid
      simp [An, An1, A0, hnum, hmid]
    else
      rw [mul_comm, ENNReal.div_mul_div_cancel hmid (measure_ne_top π _)]


-- created on 2023-10-13
-- updated on 2026-11-17
