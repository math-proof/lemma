import Mathlib
import sympy.Basic


/--
[DoubleCoset_natCard_quotient_eq_natCard_quotient_map_of_surjective](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_DoubleCoset_natCard_quotient_eq_natCard_quotient_map_of_surjective.lean)
-/
@[path]
private lemma main
  {G Q : Type*} [Group G] [Group Q]
  {f : G →* Q}
  {H K : Subgroup G}
-- given
  (hf : Function.Surjective f)
  (hH : f.ker ≤ H) :
-- imply
  Nat.card (DoubleCoset.Quotient (H : Set G) (K : Set G)) =
      Nat.card (DoubleCoset.Quotient (H.map f : Set Q) (K.map f : Set Q)) := by
-- proof
  let φ : DoubleCoset.Quotient (H : Set G) (K : Set G) → DoubleCoset.Quotient (H.map f : Set Q) (K.map f : Set Q) :=
    Quotient.map' f (fun x y hxy => by
      obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.rel_iff.mp hxy
      exact DoubleCoset.rel_iff.mpr ⟨f a, Subgroup.mem_map_of_mem f ha, f b, Subgroup.mem_map_of_mem f hb,
        by rw [map_mul, map_mul]⟩)
  have hφ : ∀ x : G, φ (DoubleCoset.mk H K x) = DoubleCoset.mk (H.map f) (K.map f) (f x) := fun _ => rfl
  refine Nat.card_congr (Equiv.ofBijective φ ⟨?_, ?_⟩)
  ·
    intro q₁ q₂ h
    induction q₁ using Quotient.inductionOn' with | h x => ?_
    induction q₂ using Quotient.inductionOn' with | h y => ?_
    change φ (DoubleCoset.mk H K x) = φ (DoubleCoset.mk H K y) at h
    rw [hφ, hφ, DoubleCoset.eq] at h
    obtain ⟨a', ha', b', hb', hy⟩ := h
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp ha'
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hb'
    change DoubleCoset.mk H K x = DoubleCoset.mk H K y
    rw [DoubleCoset.eq]
    have hn : y * (a * x * b)⁻¹ ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, ← hy, mul_inv_cancel]
    refine ⟨y * (a * x * b)⁻¹ * a, H.mul_mem (hH hn) ha, b, hb, ?_⟩
    group
  ·
    intro q
    induction q using Quotient.inductionOn' with | h z => ?_
    obtain ⟨x, rfl⟩ := hf z
    exact ⟨DoubleCoset.mk H K x, hφ x⟩


-- created on 2026-10-05
