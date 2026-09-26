import Lemma.Measure.Measurable_FrestrictLe_PiLE
open MeasureTheory Finset Measure


@[main]
private lemma main
  {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
-- given
  (n : ℕ) :
-- imply
  Measurable[Filtration.piLE n] (fun x : (i : ℕ) → X i => x n) := by
-- proof
  apply (measurable_pi_apply (⟨n, mem_Iic.2 le_rfl⟩ : Iic n)).comp (Measurable_FrestrictLe_PiLE n)


-- created on 2026-09-26