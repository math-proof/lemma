import sympy.stats.markov_samples
import sympy.Basic
import Lemma.Anchors.Time.lt.TimeAdd1
open Finset


@[main]
private lemma main
  {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]
  {d : ℕ}
  {sk : Skeleton S d} :
-- imply
  Iterates (fun n => sk.x (sk.anc.t n)) sk.x₀ sk.f sk.e₁ sk.e₂ sk.anc.β := by
-- proof
  refine ⟨fun ω => sk.hx.init ω, fun n ω => ?_⟩
  have tel : ∀ b, sk.anc.t n ≤ b → sk.x b ω = sk.x (sk.anc.t n) ω + ∑ i ∈ Ico (sk.anc.t n) b, sk.α i • sk.G (sk.x i ω) (ω (i + 1)) := fun b hb => by
    induction b, hb using Nat.le_induction with
    | base => simp
    | succ b hb ih =>
      rw [sum_Ico_succ_top hb, ← add_assoc, ← ih, sk.hx.step]
      rfl
  show sk.x (sk.anc.t (n + 1)) ω = sk.x (sk.anc.t n) ω + sk.anc.β n • (sk.f (sk.x (sk.anc.t n) ω) - sk.x (sk.anc.t n) ω) + sk.e₁ (n + 1) ω + sk.e₂ (n + 1) ω
  rw [tel _ Anchors.Time.lt.TimeAdd1.le]
  simp only [Skeleton.e₂, Skeleton.e₁, Skeleton.e₂₁, Skeleton.e₂₂, Nat.add_sub_cancel, Anchors.β, sum_smul, add_assoc, ← sum_add_distrib]
  congr 1
  refine sum_congr rfl fun i _ => ?_
  simp only [Skeleton.g, Pi.sub_apply, id, smul_sub]
  abel


-- created on 2026-09-26