import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/--
[Rep_nonempty_invariants_coind_equiv](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Rep_nonempty_invariants_coind_equiv.lean)
-/
@[path]
private lemma main
  {k G : Type} [CommRing k] [Group G]
  (H : Subgroup G)
  (N : Rep k ↥H) :
  -- imply
  Nonempty ((Rep.coind H.subtype N).ρ.invariants ≃ₗ[k] N.ρ.invariants) := by
  -- proof
  have hact : ∀ (g x : G) (f : Rep.coind H.subtype N), ((Rep.coind H.subtype N).ρ g f : G → N) x = (f : G → N) (x * g) :=
    fun _ _ _ => rfl
  have hconst : ∀ f : (Rep.coind H.subtype N).ρ.invariants, ∀ x : G, ((f : Rep.coind H.subtype N) : G → N) x = ((f : Rep.coind H.subtype N) : G → N) 1 := by
    intro f x
    have := congrArg (fun φ : Rep.coind H.subtype N => (φ : G → N) 1) (f.2 x)
    simpa [hact] using this
  have hval : ∀ f : (Rep.coind H.subtype N).ρ.invariants, ((f : Rep.coind H.subtype N) : G → N) 1 ∈ N.ρ.invariants := by
    intro f s
    have h1 := (Representation.mem_coindV H.subtype N.ρ _).mp (f : Rep.coind H.subtype N).2 s 1
    rw [mul_one] at h1
    rw [← h1]
    apply hconst f _
  have hmem : ∀ n : N.ρ.invariants, (fun _ : G => (n : N)) ∈ Representation.coindV H.subtype N.ρ := by
    intro n
    rw [Representation.mem_coindV]
    intro s _
    apply (n.2 s).symm
  have hinv : ∀ n : N.ρ.invariants, (⟨fun _ : G => (n : N), hmem n⟩ : Rep.coind H.subtype N) ∈ (Rep.coind H.subtype N).ρ.invariants := by
    intro n g
    apply Subtype.ext
    funext x
    rw [hact]
  refine ⟨LinearEquiv.ofLinearMap
    ⟨fun f => Subtype.mk (((f : Rep.coind H.subtype N) : G → N) 1) (hval f), fun _ _ => rfl, fun _ _ => rfl⟩
    ⟨fun n => Subtype.mk (Subtype.mk (fun _ : G => (n : N)) (hmem n)) (hinv n), fun _ _ => rfl, fun _ _ => rfl⟩
    ?_ ?_⟩
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
