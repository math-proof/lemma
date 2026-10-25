import Mathlib
import Mathlib.Data.Real.Sign
import Theorem.Analysis.Section_9_1.Part3
import Abbrev.Analysis.Section_9_3
set_option doc.verso.suggestions false


namespace Chapter9

/-- Connection with Mathlib filter convergence concepts -/
theorem Convergesto.iff (X:Set ℝ) (f: ℝ → ℝ) (L:ℝ) (x₀:ℝ) :
  Convergesto X f L x₀ ↔ (nhdsWithin x₀ X).Tendsto f (nhds L) := by
  unfold Convergesto Real.CloseNear Real.CloseFn nhdsWithin
  rw [LinearOrderedAddCommGroup.tendsto_nhds]
  peel with ε hε
  rw [Filter.eventually_inf_principal]
  simp [Filter.Eventually, mem_nhds_iff_exists_Ioo_subset]
  constructor
  . intro ⟨ δ, _, _ ⟩; use x₀-δ, x₀+δ, by grind
    intro _; simp; grind
  intro ⟨ l, u, ⟨ _, _ ⟩, h ⟩
  have h1 : 0 < x₀ - l := by linarith
  have h2 : 0 < u - x₀ := by linarith
  set δ := min (x₀ - l) (u - x₀)
  observe hδ1 : δ ≤ x₀ - l
  observe hδ2 : δ ≤ u - x₀
  use δ, (by positivity); intro x hxX _ _
  specialize h (show x ∈ .Ioo l u by simp; grind)
  simpa [hxX] using h

theorem Convergesto.comp {E:Set ℝ} {f: ℝ → ℝ} {L:ℝ} {x₀:ℝ} (hf: Convergesto E f L x₀) {a:ℕ → ℝ}
  (ha: ∀ n:ℕ, a n ∈ E) (hconv: Filter.atTop.Tendsto a (nhds x₀)) :
  Filter.atTop.Tendsto (fun n ↦ f (a n)) (nhds L) := by
  rw [iff_conv f L] at hf; solve_by_elim

-- Remark 9.3.11 is not quite true in Lean: the hypothesis `AdherentPt x₀ E` is safely removed
-- from most theorems (with the exception of Convergesto.uniq).

/-- Corollary 9.3.13 -/
theorem Convergesto.uniq {E:Set ℝ} {f: ℝ → ℝ} {L L':ℝ} {x₀:ℝ} (h: AdherentPt x₀ E)
  (hf: Convergesto E f L x₀) (hf': Convergesto E f L' x₀) : L = L' := by
  -- This proof is written to follow the structure of the original text.
  let ⟨ a, ha, hconv ⟩ := (limit_of_AdherentPt _ _).mp h
  exact tendsto_nhds_unique (hf.comp ha hconv) (hf'.comp ha hconv)

/-- Proposition 9.3.14 (Limit laws for functions, add) -/
theorem Convergesto.add {E:Set ℝ} {f g: ℝ → ℝ} {L M:ℝ} {x₀:ℝ}
  (hf: Convergesto E f L x₀) (hg: Convergesto E g M x₀) :
  Convergesto E (f + g) (L + M) x₀ := by
    -- This proof is written to follow the structure of the original text.
    rw [iff_conv _ _] at hf hg ⊢
    intro a ha hconv; specialize hf a ha hconv; specialize hg a ha hconv
    convert hf.add hg using 1

theorem Real.sign_def (x:ℝ) : Real.sign x = if x < 0 then -1 else if x > 0 then 1 else 0 := rfl

end Chapter9
