import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[Submodule_finite_torsionBy_pow_of_finite_torsionBy](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Submodule_finite_torsionBy_pow_of_finite_torsionBy.lean)
-/
@[path]
private lemma main
  [CommRing R] [AddCommGroup M] [Module R M]
  (a : R)
  (k : ℕ)
  -- given
  (h : Finite (Submodule.torsionBy R M a)) :
  -- imply
  Finite (Submodule.torsionBy R M (a ^ k)) := by
  -- proof
  have hS : {x : M | a • x = 0}.Finite := by
    have : {x : M | a • x = 0} = (Submodule.torsionBy R M a : Set M) := by
      ext x
      simp
    rw [this]
    apply Set.toFinite _
  suffices H : ∀ k : ℕ, {x : M | a ^ k • x = 0}.Finite by
    have hk := H k
    have : {x : M | a ^ k • x = 0} = (Submodule.torsionBy R M (a ^ k) : Set M) := by
      ext x
      simp
    rw [this] at hk
    apply hk.to_subtype
  intro k
  induction k with
  | zero =>
    refine (Set.finite_singleton (0 : M)).subset ?_
    intro x hx
    simpa using hx
  | succ k ih =>
    have hfib : ∀ y : M, {x : M | a ^ k • x = y}.Finite := by
      intro y
      obtain he | ⟨x₀, hx₀⟩ := Set.eq_empty_or_nonempty {x : M | a ^ k • x = y}
      ·
        rw [he]
        apply Set.finite_empty
      ·
        refine (ih.image fun s => x₀ + s).subset ?_
        intro x hx
        simp only [Set.mem_ofPred_eq] at hx hx₀
        refine ⟨x - x₀, ?_, by abel⟩
        simp only [Set.mem_ofPred_eq, smul_sub, hx, hx₀, sub_self]
    refine (hS.biUnion fun y _ => hfib y).subset ?_
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx
    refine Set.mem_biUnion (x := a ^ k • x) ?_ rfl
    simp only [Set.mem_ofPred_eq, smul_smul, ← pow_succ', hx]


-- created on 2026-10-20
