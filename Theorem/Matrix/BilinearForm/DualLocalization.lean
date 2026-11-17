module

public import Mathlib

public section

open LinearMap


namespace LinearMap.BilinForm

/--
[dualSubmodule_span_localization](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/BilinearForm/DualLocalization.lean)
-/
public theorem dualSubmodule_span_localization
  [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K] [AddCommGroup V] [Module A V] [Module K V] [IsScalarTower A K V]
  {B : LinearMap.BilinForm K V}
  {S : Submonoid A}
  {M : Submodule A V}
-- given
  (hS : S ≤ nonZeroDivisors A)
  (hM : M.FG)
  {Aₛ : Type*} [CommRing Aₛ] [Algebra A Aₛ] [Module Aₛ V]
  [IsScalarTower A Aₛ V] [IsLocalization S Aₛ]
  [Algebra Aₛ K] [IsScalarTower A Aₛ K] [IsScalarTower Aₛ K V] :
-- imply
  B.dualSubmodule (Submodule.span Aₛ (M : Set V)) =
    Submodule.span Aₛ (B.dualSubmodule M : Set V) := by
-- proof
  apply le_antisymm
  · intro x hx
    obtain ⟨T, hT⟩ := hM
    classical
    -- Each generator pairing lies in `Aₛ`; pick one denominator per generator.
    have hmem : ∀ u : ↥T, ∃ sp : A × S,
      B x (u : V) * algebraMap A K sp.2 = algebraMap A K sp.1 := by
      intro u
      have hmemT : (u : V) ∈ (T : Set V) := u.2
      have htM : (u : V) ∈ (M : Set V) := by
        rw [← hT]
        exact Submodule.subset_span hmemT
      have hyt : (u : V) ∈ Submodule.span Aₛ (M : Set V) :=
        Submodule.subset_span htM
      obtain ⟨c, hc⟩ := Submodule.mem_one.mp ((mem_dualSubmodule B).mp hx _ hyt)
      obtain ⟨⟨a, s⟩, hfrac⟩ := IsLocalization.surj S c
      refine ⟨(a, s), ?_⟩
      have hmap := congrArg (algebraMap Aₛ K) hfrac
      simp only [map_mul, ← IsScalarTower.algebraMap_apply] at hmap
      rw [← hc]
      exact hmap
    choose sp hsp using hmem
    -- Common denominator: product over the finite generating set.
    set s₀ : A := ∏ u : ↥T, ((sp u).2 : A) with hs₀
    have hs₀S : s₀ ∈ S := by
      rw [hs₀]
      exact Submonoid.prod_mem S (fun u _ => (sp u).2.2)
    -- `s₀ • x` lies in the original dual.
    have hsm : s₀ • x ∈ B.dualSubmodule M := by
      refine (mem_dualSubmodule B).mpr ?_
      intro y hy
      rw [← hT] at hy
      refine Submodule.span_induction (p := fun y _ => B (s₀ • x) y ∈ (1 : Submodule A K))
        ?_ ?_ ?_ ?_ (x := y) hy
      · intro z hz
        have hzT : z ∈ T := hz
        let u : ↥T := ⟨z, hzT⟩
        have key : B x z * algebraMap A K s₀ ∈ algebraMap A K '' Set.univ := by
          have hdiv : s₀ = ((sp u).2 : A) * ∏ v ∈ Finset.univ.erase u, ((sp v).2 : A) :=
            (Finset.mul_prod_erase _ _ (Finset.mem_univ u)).symm
          refine ⟨(sp u).1 * ∏ v ∈ Finset.univ.erase u, ((sp v).2 : A),
            Set.mem_univ _, ?_⟩
          rw [hdiv, map_mul, map_mul, ← mul_assoc, hsp u]
        obtain ⟨a, _, ha⟩ := key
        rw [BilinForm.smul_left_of_tower, Algebra.smul_def, mul_comm]
        exact Submodule.mem_one.mpr ⟨a, ha⟩
      · simp [BilinForm.zero_right]
      · intro a b _ _ ha hb
        rw [BilinForm.add_right]
        exact Submodule.add_mem (1 : Submodule A K) ha hb
      · intro r z _ hz
        rw [BilinForm.smul_right_of_tower]
        exact Submodule.smul_mem _ _ hz
    -- `algebraMap A Aₛ s₀` is a unit, so `x` is an `Aₛ`-multiple of `s₀ • x`.
    have hunit : IsUnit (algebraMap A Aₛ s₀) :=
      IsLocalization.map_units Aₛ ⟨s₀, hs₀S⟩
    obtain ⟨u, hu⟩ := hunit
    have hrec : x = ((u⁻¹ : Units Aₛ) : Aₛ) • (s₀ • x) := by
      change x = (u⁻¹ : Units Aₛ) • (s₀ • x)
      rw [eq_inv_smul_iff]
      change (u : Aₛ) • x = s₀ • x
      rw [hu, IsScalarTower.algebraMap_smul Aₛ s₀ x]
    rw [hrec]
    apply Submodule.smul_mem
    exact Submodule.subset_span hsm
  · rw [Submodule.span_le]
    intro x hx
    refine (mem_dualSubmodule B).mpr ?_
    intro y hy
    refine Submodule.span_induction (p := fun y _ => B x y ∈ (1 : Submodule Aₛ K))
      ?_ ?_ ?_ ?_ (x := y) hy
    · intro z hz
      obtain ⟨a, ha⟩ := Submodule.mem_one.mp ((mem_dualSubmodule B).mp hx z hz)
      exact Submodule.mem_one.mpr ⟨algebraMap A Aₛ a, by
        rw [← IsScalarTower.algebraMap_apply A Aₛ K]
        exact ha⟩
    · simp [BilinForm.zero_right]
    · intro a b _ _ ha hb
      rw [BilinForm.add_right]
      exact Submodule.add_mem (1 : Submodule Aₛ K) ha hb
    · intro r z _ hz
      rw [BilinForm.smul_right_of_tower]
      exact Submodule.smul_mem _ _ hz

end LinearMap.BilinForm


-- created on 2026-10-20
-- updated on 2026-11-16
