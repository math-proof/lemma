import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.Analysis.InnerProductSpace.Dual
import Def.Analysis.Convex.LinearProgrammingDuality
/-!
# Strong linear programming duality

A feasible bounded-above primal `max { c ⬝ᵥ x | x ≥ 0, A *ᵥ x ≤ b }` attains
its supremum, and there is a dual-feasible `y ≥ 0` with `c ≤ Aᵀ *ᵥ y` and
equal objective value `c ⬝ᵥ x = b ⬝ᵥ y`.

Informal source: George B. Dantzig, *Linear Programming and Extensions*,
Princeton University Press, 1963, strong duality theorem.
-/


namespace Convex.LPDuality

open scoped Topology Matrix

open Finset Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

section Farkas

variable {p q : ℕ}

/-- Column generators lie in the cone. -/
lemma lpCone_gen_col (M : Matrix (Fin p) (Fin q) ℝ) (e : Fin q → ℝ)
    (i : Fin q) : ((fun j => M j i), e i) ∈ lpCone M e := by
  refine ⟨Pi.single (M := fun _ => ℝ) i 1, fun k => ?_, 0, fun j => by simp,
    0, le_rfl, ?_, ?_⟩
  · rw [Pi.single_apply]
    split_ifs with h
    · exact zero_le_one
    · exact le_rfl
  · change (fun j => M j i) = M.mulVec (Pi.single (M := fun _ => ℝ) i 1) + 0
    rw [add_zero]
    funext j
    change M j i = (∑ k, M j k * Pi.single (M := fun _ => ℝ) i 1 k)
    rw [Finset.sum_eq_single i]
    · rw [Pi.single_eq_same, mul_one]
    · intro b _ hb
      have h0 : Pi.single (M := fun _ => ℝ) i 1 b = 0 := by
        rw [Pi.single_apply, ite_eq_right hb]
      rw [h0, mul_zero]
    · intro hcon
      exact absurd (Finset.mem_univ i) hcon
  · change e i = e ⬝ᵥ Pi.single (M := fun _ => ℝ) i 1 - 0
    rw [sub_zero]
    exact (dotProduct_single_one e i).symm

/-- Slack generators lie in the cone. -/
lemma lpCone_gen_slack (M : Matrix (Fin p) (Fin q) ℝ) (e : Fin q → ℝ)
    (j : Fin p) : (Pi.single (M := fun _ => ℝ) j 1, 0) ∈ lpCone M e := by
  have hM0 : M.mulVec (0 : Fin q → ℝ) = 0 := by
    funext k
    change (∑ i, M k i * ((0 : Fin q → ℝ) i)) = (0 : Fin p → ℝ) k
    simp
  have hd0 : e ⬝ᵥ (0 : Fin q → ℝ) = 0 := by
    change (∑ i, e i * ((0 : Fin q → ℝ) i)) = 0
    simp
  refine ⟨0, fun i => by simp, Pi.single (M := fun _ => ℝ) j 1, fun k => ?_,
    0, le_rfl, ?_, ?_⟩
  · rw [Pi.single_apply]
    split_ifs with h
    · exact zero_le_one
    · exact le_rfl
  · change Pi.single (M := fun _ => ℝ) j 1
      = M.mulVec (0 : Fin q → ℝ) + Pi.single (M := fun _ => ℝ) j 1
    rw [hM0, zero_add]
  · change (0 : ℝ) = e ⬝ᵥ (0 : Fin q → ℝ) - 0
    rw [hd0, sub_zero]

/-- The value-direction generator lies in the cone. -/
lemma lpCone_gen_val (M : Matrix (Fin p) (Fin q) ℝ) (e : Fin q → ℝ) :
    ((0 : Fin p → ℝ), -1) ∈ lpCone M e := by
  have hM0 : M.mulVec (0 : Fin q → ℝ) = (0 : Fin p → ℝ) := by
    funext k
    change (∑ i, M k i * ((0 : Fin q → ℝ) i)) = (0 : Fin p → ℝ) k
    simp
  have hd0 : e ⬝ᵥ (0 : Fin q → ℝ) = 0 := by
    change (∑ i, e i * ((0 : Fin q → ℝ) i)) = 0
    simp
  refine ⟨0, fun i => by simp, 0, fun j => by simp, 1, zero_le_one, ?_, ?_⟩
  · change (0 : Fin p → ℝ) = M.mulVec (0 : Fin q → ℝ) + 0
    rw [hM0, add_zero]
  · change (-1 : ℝ) = e ⬝ᵥ (0 : Fin q → ℝ) - 1
    rw [hd0]
    exact (zero_sub 1).symm

/-- The cone contains the origin. -/
lemma lpCone_zero (M : Matrix (Fin p) (Fin q) ℝ) (e : Fin q → ℝ) :
    ((0 : Fin p → ℝ), 0) ∈ lpCone M e := by
  have hM0 : M.mulVec (0 : Fin q → ℝ) = (0 : Fin p → ℝ) := by
    funext k
    change (∑ i, M k i * ((0 : Fin q → ℝ) i)) = (0 : Fin p → ℝ) k
    simp
  have hd0 : e ⬝ᵥ (0 : Fin q → ℝ) = 0 := by
    change (∑ i, e i * ((0 : Fin q → ℝ) i)) = 0
    simp
  refine ⟨0, fun i => by simp, 0, fun j => by simp, 0, le_rfl, ?_, ?_⟩
  · change (0 : Fin p → ℝ) = M.mulVec (0 : Fin q → ℝ) + 0
    rw [hM0, add_zero]
  · change (0 : ℝ) = e ⬝ᵥ (0 : Fin q → ℝ) - 0
    rw [hd0, sub_zero]

/-- The cone is closed under addition. -/
lemma lpCone_add (M : Matrix (Fin p) (Fin q) ℝ) (e : Fin q → ℝ)
    (a b : (Fin p → ℝ) × ℝ) :
    a ∈ lpCone M e → b ∈ lpCone M e → a + b ∈ lpCone M e := by
  rintro ⟨x₁, hx₁, s₁, hs₁, r₁, hr₁, h1a, h1b⟩
    ⟨x₂, hx₂, s₂, hs₂, r₂, hr₂, h2a, h2b⟩
  refine ⟨x₁ + x₂, fun i => add_nonneg (hx₁ i) (hx₂ i),
    s₁ + s₂, fun j => add_nonneg (hs₁ j) (hs₂ j),
    r₁ + r₂, add_nonneg hr₁ hr₂, ?_, ?_⟩
  · change a.1 + b.1 = M.mulVec (x₁ + x₂) + (s₁ + s₂)
    have e1 : M.mulVec (x₁ + x₂) = M.mulVec x₁ + M.mulVec x₂ :=
      map_add (Matrix.mulVecLin M) x₁ x₂
    rw [e1, h1a, h2a]
    abel
  · change a.2 + b.2 = e ⬝ᵥ (x₁ + x₂) - (r₁ + r₂)
    have e2 : e ⬝ᵥ (x₁ + x₂) = e ⬝ᵥ x₁ + e ⬝ᵥ x₂ :=
      dotProduct_add _ _ _
    rw [e2, h1b, h2b]
    ring

/-- The cone is closed under nonnegative scaling. -/
lemma lpCone_smul (M : Matrix (Fin p) (Fin q) ℝ) (e : Fin q → ℝ)
    (a : ℝ) (ha : 0 ≤ a) (y : (Fin p → ℝ) × ℝ) :
    y ∈ lpCone M e → a • y ∈ lpCone M e := by
  rintro ⟨x, hx, s, hs, r, hr, h1, h2⟩
  refine ⟨a • x, fun i => smul_nonneg ha (hx i),
    a • s, fun j => smul_nonneg ha (hs j),
    a * r, mul_nonneg ha hr, ?_, ?_⟩
  · change a • y.1 = M.mulVec (a • x) + a • s
    have e1 : M.mulVec (a • x) = a • M.mulVec x :=
      map_smul (Matrix.mulVecLin M) a x
    rw [e1, h1, smul_add]
  · change a • y.2 = e ⬝ᵥ (a • x) - a * r
    have e2 : e ⬝ᵥ (a • x) = a • (e ⬝ᵥ x) :=
      dotProduct_smul _ _ _
    rw [e2, h2]
    simp only [smul_eq_mul]
    ring

/-- Generated cone points lie in the cone. -/
lemma hull_subset_lpCone (M : Matrix (Fin p) (Fin q) ℝ) (e : Fin q → ℝ) :
    (PointedCone.hull ℝ (↑(lpConeGens M e) : Set ((Fin p → ℝ) × ℝ)) :
      Set ((Fin p → ℝ) × ℝ)) ⊆ lpCone M e := by
  intro y hy
  obtain ⟨c, hsupp, hc, hcomb⟩ := PointedCone.mem_hull_set.mp hy
  have hterm : ∀ v ∈ c.support, c v • v ∈ lpCone M e := by
    intro v hv
    have hmem : v ∈ lpConeGens M e := hsupp hv
    unfold lpConeGens at hmem
    rw [Finset.mem_union, Finset.mem_union] at hmem
    obtain (h1 | h2) | hk := hmem
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h1
      rw [← hi]
      exact lpCone_smul M e _ (hc _) _ (lpCone_gen_col M e i)
    · obtain ⟨j, _, hj⟩ := Finset.mem_image.mp h2
      rw [← hj]
      exact lpCone_smul M e _ (hc _) _ (lpCone_gen_slack M e j)
    · rw [Finset.mem_singleton] at hk
      rw [hk]
      exact lpCone_smul M e _ (hc _) _ (lpCone_gen_val M e)
  have hsum : (∑ v ∈ c.support, c v • v) ∈ lpCone M e :=
    Finset.sum_induction _ _ (lpCone_add M e) (lpCone_zero M e) hterm
  have hyeq : y = ∑ v ∈ c.support, c v • v := by
    rw [← hcomb]
    change c.sum (fun v a => a • v) = ∑ v ∈ c.support, c v • v
    rfl
  rw [hyeq]
  exact hsum

end Farkas
end Convex.LPDuality
