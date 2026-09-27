import sympy.stats.markov_chain_trajectory
import sympy.Basic
open MeasureTheory ProbabilityTheory Finset Kernel


@[main]
private lemma main
  [MeasurableSpace S]
  {n m : ℕ}
-- given
  (h : n ≤ m)
  (M : HomMarkovChainSpec S) :
-- imply
  (partialTraj (X := fun _ => S) M.expand_kernel n m).map (fun x => x ⟨m, mem_Iic.2 le_rfl⟩) =
    (M.kernel ^ (m - n)).comap_last n := by
-- proof
  have := M.markov_kernel
  induction m, h using Nat.le_induction with
  | base =>
    ext x : 1
    rw [partialTraj_self, Kernel.id_map (measurable_pi_apply _), Nat.sub_self, pow_zero]
    rfl
  | succ m h ih =>
    rw [partialTraj_succ_eq_comp h, map_comp, map_partialTraj_succ_self]
    rw [HomMarkovChainSpec.expand_kernel, comap_last, ← Kernel.comp_map (partialTraj (X := fun _ => S) M.expand_kernel n m) M.kernel (measurable_pi_apply (⟨m, mem_Iic.2 le_rfl⟩ : Iic m)), ih, Nat.sub_add_comm h, pow_succ']
    rfl


-- created on 2026-09-26