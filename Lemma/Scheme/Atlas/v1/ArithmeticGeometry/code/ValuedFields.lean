import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.ValuedFields
open Filter Topology


/--
[seqConvergesTo_iff_forall_eps](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ValuedFields.lean)
-/
@[path]
lemma seqConvergesTo_iff_forall_eps
  [SeminormedAddCommGroup k]
  {x : ℕ → k}
  {ℓ : k} :
-- imply
  SeqConvergesTo x ℓ ↔ ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, dist (x n) ℓ < ε :=
-- proof
  Metric.tendsto_atTop

/--
[seqConvergesTo_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ValuedFields.lean)
-/
@[path]
lemma seqConvergesTo_add
  [NormedField k]
  {x y : ℕ → k}
  {a b : k}
-- given
  (hx : SeqConvergesTo x a)
  (hy : SeqConvergesTo y b) :
-- imply
  SeqConvergesTo (x + y) (a + b) := by
-- proof
  unfold SeqConvergesTo at *
  exact Filter.Tendsto.add hx hy
section CauchySequence
variable {k : Type*} [NormedField k]

/--
[isCauchySeq_iff_cauchySeq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ValuedFields.lean)
-/
@[path]
lemma isCauchySeq_iff_cauchySeq
  [NormedField k]
  {x : ℕ → k} :
-- imply
  IsCauchySeq x ↔ CauchySeq x := by
-- proof
  simp only [IsCauchySeq, ← dist_eq_norm]
  exact Metric.cauchySeq_iff.symm
end CauchySequence
section Theorem710
variable {k : Type*} [NormedField k]

/--
[convergent_imp_cauchy](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ValuedFields.lean)
-/
@[path]
lemma convergent_imp_cauchy
  [NormedField k]
  {x : ℕ → k}
  {ℓ : k}
-- given
  (hx : SeqConvergesTo x ℓ) :
-- imply
  CauchySeq x :=
-- proof
  hx.cauchySeq
end Theorem710

/--
[seqEquiv_iff_forall_eps_norm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ValuedFields.lean)
-/
@[path]
lemma seqEquiv_iff_forall_eps_norm
  [SeminormedAddCommGroup k]
  {a b : ℕ → k} :
-- imply
  SeqEquiv a b ↔ ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ‖a n - b n‖ < ε := by
-- proof
  rw [SeqEquiv, Metric.tendsto_atTop]
  simp only [dist_zero_right]
section CompleteField
variable {k : Type*} [NormedField k]

/--
[dense_iff_forall_norm_sub_lt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ValuedFields.lean)
-/
@[path]
lemma dense_iff_forall_norm_sub_lt
  [NormedField k]
  {S : Set k} :
-- imply
  Dense S ↔ ∀ x : k, ∀ ε > 0, ∃ y ∈ S, ‖x - y‖ < ε := by
-- proof
  rw [Metric.dense_iff]
  constructor
  · intro h x ε hε
    obtain ⟨y, hy_ball, hy_S⟩ := h x ε hε
    rw [Metric.mem_ball, dist_comm] at hy_ball
    exact ⟨y, hy_S, by rwa [dist_eq_norm] at hy_ball⟩
  · intro h x ε hε
    obtain ⟨y, hy_S, hy_norm⟩ := h x ε hε
    exact ⟨y, by rwa [Metric.mem_ball, dist_comm, dist_eq_norm], hy_S⟩
section Completion
variable (k : Type*) [NormedField k] [CompletableTopField k]

/--
[denseRange_completion_coe](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ValuedFields.lean)
-/
@[path]
lemma denseRange_completion_coe
  {k : Type*}
  [NormedField k] :
-- imply
  DenseRange (UniformSpace.Completion.coe' : k → UniformSpace.Completion k) :=
-- proof
  UniformSpace.Completion.denseRange_coe
section Corollary717
variable (k : Type*) [NormedField k] [CompletableTopField k]
omit [CompletableTopField k] in
variable {k}
variable (k' : Type*) [NormedField k'] [CompleteSpace k']

/--
[cauchy_seq_completion_equiv_from_k](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ValuedFields.lean)
-/
@[path]
lemma cauchy_seq_completion_equiv_from_k
  {k : Type*}
  [NormedField k]
  {z : ℕ → UniformSpace.Completion k}
-- given
  (hz : CauchySeq z) :
-- imply
  ∃ x : ℕ → k, CauchySeq (fun n => (↑(x n) : UniformSpace.Completion k)) ∧ SeqEquiv z (fun n => ↑(x n)) := by
-- proof
  have hd := UniformSpace.Completion.denseRange_coe (α := k)
  choose x hx using fun n => hd.exists_dist_lt (z n) (by positivity : (0:ℝ) < 1 / (↑n + 1))
  refine ⟨x, ?_, ?_⟩
  ·
    rw [Metric.cauchySeq_iff]
    intro ε hε
    rw [Metric.cauchySeq_iff] at hz
    obtain ⟨N₁, hN₁⟩ := hz (ε / 3) (by linarith)
    obtain ⟨N₂, hN₂⟩ := exists_nat_gt (3 / ε)
    refine ⟨max N₁ N₂, fun m hm n hn => ?_⟩
    have hm₂ : (m : ℕ) ≥ N₂ := le_of_max_le_right hm
    have hn₂ : (n : ℕ) ≥ N₂ := le_of_max_le_right hn
    have hm_approx : 1 / ((m : ℝ) + 1) < ε / 3 := by
      rw [div_lt_div_iff₀ (by positivity : (0:ℝ) < ↑m + 1) (by linarith : (0:ℝ) < 3)]
      have : 3 / ε < ↑m + 1 := by
        calc 3 / ε < ↑N₂ := hN₂
          _ ≤ ↑m := Nat.cast_le.mpr hm₂
          _ ≤ ↑m + 1 := le_add_of_nonneg_right (by positivity)
      rw [div_lt_iff₀ hε] at this; linarith
    have hn_approx : 1 / ((n : ℝ) + 1) < ε / 3 := by
      rw [div_lt_div_iff₀ (by positivity : (0:ℝ) < ↑n + 1) (by linarith : (0:ℝ) < 3)]
      have : 3 / ε < ↑n + 1 := by
        calc 3 / ε < ↑N₂ := hN₂
          _ ≤ ↑n := Nat.cast_le.mpr hn₂
          _ ≤ ↑n + 1 := le_add_of_nonneg_right (by positivity)
      rw [div_lt_iff₀ hε] at this; linarith
    calc dist (↑(x m) : UniformSpace.Completion k) (↑(x n))
      ≤ dist (↑(x m)) (z m) + dist (z m) (↑(x n)) := dist_triangle _ _ _
      _ ≤ dist (↑(x m)) (z m) + (dist (z m) (z n) + dist (z n) (↑(x n))) := by
        linarith [dist_triangle (z m) (z n) (↑(x n) : UniformSpace.Completion k)]
      _ < ε / 3 + (ε / 3 + ε / 3) := by
        have h1 : dist (↑(x m)) (z m) < 1 / (↑m + 1) := by rw [dist_comm]; exact hx m
        have h2 : dist (z m) (z n) < ε / 3 :=
          hN₁ m (le_of_max_le_left hm) n (le_of_max_le_left hn)
        have h3 : dist (z n) (↑(x n)) < 1 / (↑n + 1) := hx n
        linarith
      _ = ε := by ring
  ·
    show Filter.Tendsto (fun n => z n - ↑(x n)) Filter.atTop (nhds 0)
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
    refine ⟨N, fun n hn => ?_⟩
    rw [dist_zero_right]
    have hn_bound : 1 / ((n : ℝ) + 1) < ε := by
      rw [div_lt_iff₀ (by positivity : (0:ℝ) < ↑n + 1)]
      have : 1 / ε < ↑n + 1 := by
        calc 1 / ε < ↑N := hN
          _ ≤ ↑n := Nat.cast_le.mpr hn
          _ ≤ ↑n + 1 := le_add_of_nonneg_right (by positivity)
      rw [div_lt_iff₀ hε] at this; linarith
    calc ‖z n - ↑(x n)‖ = dist (z n) (↑(x n)) := (dist_eq_norm _ _).symm
      _ < 1 / (↑n + 1) := hx n
      _ < ε := hn_bound


-- created on 2026-10-23
