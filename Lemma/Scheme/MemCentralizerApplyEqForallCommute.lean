import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[Representation_existsUnique_mem_centralizer_apply_eq_of_forall_commute](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Representation_existsUnique_mem_centralizer_apply_eq_of_forall_commute.lean)
-/
@[path]
private lemma main
  [Field k] [Group Δ] [AddCommGroup V] [Module k V]
  (ρ : Representation k Δ V)
  (hsimple : ∀ W : Submodule k V, (∀ (d : Δ) (v : V), v ∈ W → ρ d v ∈ W) → W = ⊥ ∨ W = ⊤)
  (hcomm : ∀ a b : Δ, ρ a * ρ b = ρ b * ρ a)
  (v : V) (hv : v ≠ 0) (w : V) :
  -- imply
  ∃! φ : Module.End k V, (∀ d : Δ, φ * ρ d = ρ d * φ) ∧ φ v = w := by
  -- proof
  classical
  let S : Set V := Set.range (fun d : Δ => ρ d v)
  have hstab : ∀ (d : Δ) (x : V), x ∈ Submodule.span k S → ρ d x ∈ Submodule.span k S := by
    intro d x hx
    have hle : (Submodule.span k S).map (ρ d) ≤ Submodule.span k S := by
      rw [Submodule.map_span]
      apply Submodule.span_mono
      rintro _ ⟨_, ⟨d', rfl⟩, rfl⟩
      refine ⟨d * d', ?_⟩
      show ρ (d * d') v = ρ d (ρ d' v)
      rw [map_mul, Module.End.mul_apply]
    refine hle (Submodule.mem_map_of_mem hx)
  have htop : Submodule.span k S = ⊤ := by
    obtain h | h := hsimple _ hstab
    ·
      exfalso
      apply hv
      have hvS : v ∈ Submodule.span k S := Submodule.subset_span ⟨1, by simp⟩
      rw [h] at hvS
      apply (Submodule.mem_bot k).mp hvS
    ·
      apply h
  have hw : w ∈ Submodule.span k S := by rw [htop]; apply Submodule.mem_top
  obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).mp hw
  let φ : Module.End k V := c.sum fun d a => a • ρ d
  have hφv : φ v = w := by
    show (c.sum fun d a => a • ρ d) v = w
    rw [Finsupp.sum, LinearMap.sum_apply]
    simp only [LinearMap.smul_apply]
    apply hc
  have hφcomm : ∀ d : Δ, φ * ρ d = ρ d * φ := by
    intro d
    show (c.sum fun d a => a • ρ d) * ρ d = ρ d * (c.sum fun d a => a • ρ d)
    rw [Finsupp.sum, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d' _
    rw [smul_mul_assoc, mul_smul_comm, hcomm]
  refine ⟨φ, ⟨hφcomm, hφv⟩, ?_⟩
  rintro φ' ⟨h1, h2⟩
  have hker : ∀ (d : Δ) (x : V), x ∈ LinearMap.ker (φ' - φ) → ρ d x ∈ LinearMap.ker (φ' - φ) := by
    intro d x hx
    rw [LinearMap.mem_ker] at hx ⊢
    have e1 : φ' (ρ d x) = ρ d (φ' x) := by
      have := congrArg (fun f : Module.End k V => f x) (h1 d)
      simpa [Module.End.mul_apply] using this
    have e2 : φ (ρ d x) = ρ d (φ x) := by
      have := congrArg (fun f : Module.End k V => f x) (hφcomm d)
      simpa [Module.End.mul_apply] using this
    rw [LinearMap.sub_apply] at hx ⊢
    rw [e1, e2, ← map_sub, hx, map_zero]
  obtain h | h := hsimple _ hker
  ·
    exfalso
    apply hv
    have : v ∈ LinearMap.ker (φ' - φ) := by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, h2, hφv, sub_self]
    rw [h] at this
    apply (Submodule.mem_bot k).mp this
  ·
    have : φ' - φ = 0 := LinearMap.ker_eq_top.mp h
    refine sub_eq_zero.mp this


-- created on 2026-10-20
