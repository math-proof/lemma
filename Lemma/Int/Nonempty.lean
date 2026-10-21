import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[Rep_nonempty_invariants_coind_linearEquiv_invariants](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Rep_nonempty_invariants_coind_linearEquiv_invariants.lean)
-/
@[path]
private lemma main
  {k G : Type u} [CommRing k] [Group G]
  (S : Subgroup G)
  (N : Rep k S) :
  -- imply
  Nonempty ((Rep.coind S.subtype N).ρ.invariants ≃ₗ[k] N.ρ.invariants) := by
  -- proof
  classical
  have hconst : ∀ f : (Rep.coind S.subtype N).ρ.invariants, ∀ x : G, ((f : Rep.coind S.subtype N) : G → N) x = ((f : Rep.coind S.subtype N) : G → N) 1 := by
    intro f x
    have := congrArg (fun h : Rep.coind S.subtype N => (h : G → N) 1) (f.2 x)
    simpa using this
  refine ⟨LinearEquiv.ofLinearMap
    ⟨fun f => Subtype.mk (((f : Rep.coind S.subtype N) : G → N) 1) (fun s => ?_), fun _ _ => rfl, fun _ _ => rfl⟩
    ⟨fun n => Subtype.mk (Subtype.mk (fun _ => (n : N)) (fun s _ => (n.2 s).symm)) (fun g => rfl), fun _ _ => rfl, fun _ _ => rfl⟩
    ?_ ?_⟩
  ·
    intro f s
    have h := (f : Rep.coind S.subtype N).2 s 1
    rw [Subgroup.coe_subtype, mul_one] at h
    rw [← h]
    apply hconst f s
  ·
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    apply Subtype.ext
    funext x
    apply (hconst f x).symm
  ·
    apply LinearMap.ext
    intro n
    rfl


-- created on 2026-10-20
