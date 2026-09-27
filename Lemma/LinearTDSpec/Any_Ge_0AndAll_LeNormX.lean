import sympy.stats.linear_td
import sympy.Basic
open Finset


@[main]
private lemma main
  {S : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S]
  {d : ℕ}
  {spec : LinearTDSpec S d} :
-- imply
  ∃ C, 0 ≤ C ∧ ∀ s, ‖spec.x s‖ ≤ C :=
-- proof
  ⟨(∑ s, ‖spec.x s‖), sum_nonneg fun _ _ => norm_nonneg _, fun s => single_le_sum (fun s _ => norm_nonneg (spec.x s)) (mem_univ s)⟩


-- created on 2026-09-26
