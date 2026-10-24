import Mathlib
import sympy.Basic
open CategoryTheory groupCohomology


/--
[groupCohomology_exists_submodule_mem_iff_conjInvariant](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_groupCohomology_exists_submodule_mem_iff_conjInvariant.lean)
-/
@[path]
private lemma main
  {k G : Type u} [CommRing k] [Group G]
  {A : Rep.{u} k G}
  {S : Subgroup G} :
-- imply
  ∃ V : Submodule k (H1 (Rep.res S.subtype A)), ∀ x, x ∈ V ↔
      ∃ c : cocycles₁ (Rep.res S.subtype A), H1π _ c = x ∧
        ∀ g : G, ∃ a : A, ∀ s t : S, (g⁻¹ * s * g : G) = t →
          A.ρ g (c t) - c s = A.ρ (s : G) a - a := by
-- proof
  classical
    let P : cocycles₁ (Rep.res S.subtype A) → Prop := fun c =>
      ∀ g : G, ∃ a : A, ∀ s t : S, (g⁻¹ * s * g : G) = t → A.ρ g (c t) - c s = A.ρ (s : G) a - a
    have hP0 : P 0 := fun g => ⟨0, fun s t _ => by
      rw [show (0 : cocycles₁ (Rep.res S.subtype A)) t = 0 from rfl,
        show (0 : cocycles₁ (Rep.res S.subtype A)) s = 0 from rfl, map_zero, map_zero, sub_zero]⟩
    have hPadd : ∀ c c', P c → P c' → P (c + c') := by
      intro c c' hc hc' g
      obtain ⟨a, ha⟩ := hc g
      obtain ⟨a', ha'⟩ := hc' g
      refine ⟨a + a', fun s t hst => ?_⟩
      have e1 := ha s t hst
      have e2 := ha' s t hst
      have hadd : ∀ u : S, (c + c') u = c u + c' u := fun u => rfl
      rw [hadd, hadd, map_add]
      calc
        _ = (A.ρ g (c t) - c s) + (A.ρ g (c' t) - c' s) := by abel
        _ = (A.ρ (s : G) a - a) + (A.ρ (s : G) a' - a') := by rw [e1, e2]
        _ = A.ρ (s : G) (a + a') - (a + a') := by rw [map_add]; abel
    have hPsmul : ∀ (r : k) c, P c → P (r • c) := by
      intro r c hc g
      obtain ⟨a, ha⟩ := hc g
      refine ⟨r • a, fun s t hst => ?_⟩
      have hsm : ∀ u : S, (r • c) u = r • c u := fun u => rfl
      rw [hsm, hsm, map_smul, map_smul, ← smul_sub, ha s t hst, smul_sub]
    refine ⟨{ carrier := {x | ∃ c, H1π _ c = x ∧ P c}
      zero_mem' := ⟨0, map_zero _, hP0⟩
      add_mem' := ?_
      smul_mem' := ?_ }, fun x => Iff.rfl⟩
    ·
      rintro x y ⟨c, rfl, hc⟩ ⟨c', rfl, hc'⟩
      exact ⟨c + c', map_add _ _ _, hPadd c c' hc hc'⟩
    ·
      rintro r x ⟨c, rfl, hc⟩
      exact ⟨r • c, map_smul _ _ _, hPsmul r c hc⟩


-- created on 2026-10-23
