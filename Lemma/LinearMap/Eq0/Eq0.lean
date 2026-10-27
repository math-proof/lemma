import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma bilin_pow_apply [Field F] [AddCommGroup V] [Module F V] (B : LinearMap.BilinForm F V) (g : Module.End F V) (hadj : ∀ x y, B (g x) y = B x (g y)) (n : ℕ) (x y : V) : B ((g ^ n) x) y = B x ((g ^ n) y) := by
  induction n generalizing x y
  ·
    simp
  ·
    rename_i n ih
    rw [pow_succ, Module.End.mul_apply, ih, hadj, ← Module.End.mul_apply, ← pow_succ', ← pow_succ]
private lemma mem_iSup_ker_pow_iff [Field F] [AddCommGroup V] [Module F V] (g : Module.End F V) (x : V) : x ∈ (⨆ n : ℕ, LinearMap.ker (g ^ n)) ↔ ∃ n : ℕ, (g ^ n) x = 0 := by
  have hdir : Directed (· ≤ ·) (fun n : ℕ => LinearMap.ker (g ^ n)) := Monotone.directed_le fun m n h => by simpa using g.iterateKer.monotone h
  rw [Submodule.mem_iSup_of_directed _ hdir]
  simp [LinearMap.mem_ker]
private lemma bilin_eq_zero_of_mem_iSup_ker_of_mem_iInf_range [Field F] [AddCommGroup V] [Module F V] (B : LinearMap.BilinForm F V) (g : Module.End F V) (hadj : ∀ x y, B (g x) y = B x (g y)) {x w : V} (hx : x ∈ ⨆ n : ℕ, LinearMap.ker (g ^ n)) (hw : w ∈ ⨅ n : ℕ, LinearMap.range (g ^ n)) : B x w = 0 ∧ B w x = 0 := by
  obtain ⟨n, hn⟩ := (mem_iSup_ker_pow_iff g x).mp hx
  obtain ⟨w', rfl⟩ : w ∈ LinearMap.range (g ^ n) := (Submodule.mem_iInf _).mp hw n
  refine ⟨?_, ?_⟩
  ·
    rw [← bilin_pow_apply B g hadj, hn, map_zero, LinearMap.zero_apply]
  ·
    rw [bilin_pow_apply B g hadj, hn, map_zero]
private lemma nondegenerate_restrict_iSup_ker_pow [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V] (B : LinearMap.BilinForm F V) (hBl : ∀ x, (∀ y, B x y = 0) → x = 0) (hBr : ∀ y, (∀ x, B x y = 0) → y = 0) (g : Module.End F V) (hadj : ∀ x y, B (g x) y = B x (g y)) : (∀ x ∈ ⨆ n : ℕ, LinearMap.ker (g ^ n), (∀ y ∈ ⨆ n : ℕ, LinearMap.ker (g ^ n), B x y = 0) → x = 0) ∧ (∀ y ∈ ⨆ n : ℕ, LinearMap.ker (g ^ n), (∀ x ∈ ⨆ n : ℕ, LinearMap.ker (g ^ n), B x y = 0) → y = 0) := by
  have hc : IsCompl (⨆ n : ℕ, LinearMap.ker (g ^ n)) (⨅ n : ℕ, LinearMap.range (g ^ n)) := g.isCompl_iSup_ker_pow_iInf_range_pow
  have hsplit : ∀ v : V, ∃ k ∈ ⨆ n : ℕ, LinearMap.ker (g ^ n), ∃ w ∈ ⨅ n : ℕ, LinearMap.range (g ^ n), k + w = v := fun v => Submodule.mem_sup.mp (hc.sup_eq_top ▸ Submodule.mem_top (x := v))
  refine ⟨fun x hx hxK => hBl x fun v => ?_, fun y hy hyK => hBr y fun v => ?_⟩
  ·
    obtain ⟨k, hk, w, hw, rfl⟩ := hsplit v
    rw [map_add, hxK k hk, (bilin_eq_zero_of_mem_iSup_ker_of_mem_iInf_range B g hadj hx hw).1, add_zero]
  ·
    obtain ⟨k, hk, w, hw, rfl⟩ := hsplit v
    rw [map_add, LinearMap.add_apply, hyK k hk, (bilin_eq_zero_of_mem_iSup_ker_of_mem_iInf_range B g hadj hy hw).2, add_zero]
/--
[LevelRaising_nondegenerate_restrict_iSup_ker_pow](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_LevelRaising_nondegenerate_restrict_iSup_ker_pow.lean)
-/
@[path]
private lemma main
  [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  (B : LinearMap.BilinForm F V)
  (hBl : ∀ x, (∀ y, B x y = 0) → x = 0) (hBr : ∀ y, (∀ x, B x y = 0) → y = 0)
  (g : Module.End F V) (hadj : ∀ x y, B (g x) y = B x (g y)) :
  -- imply
  (∀ x ∈ ⨆ n : ℕ, LinearMap.ker (g ^ n), (∀ y ∈ ⨆ n : ℕ, LinearMap.ker (g ^ n), B x y = 0) → x = 0) ∧ (∀ y ∈ ⨆ n : ℕ, LinearMap.ker (g ^ n), (∀ x ∈ ⨆ n : ℕ, LinearMap.ker (g ^ n), B x y = 0) → y = 0) := nondegenerate_restrict_iSup_ker_pow B hBl hBr g hadj


-- created on 2026-10-20
