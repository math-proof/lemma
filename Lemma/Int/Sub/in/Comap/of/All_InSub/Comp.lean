import Mathlib
import sympy.Basic


/--
[RingHom_map_sub_self_mem_comap_of_comp_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_RingHom_map_sub_self_mem_comap_of_comp_eq.lean)
-/
@[path]
private lemma main
  [CommRing C] [CommRing C']
  {c : C →+* C'}
  {τ : C →+* C}
  {τ' : C' →+* C'}
  {y' : Ideal C'}
  {a : C}
-- given
  (hcomm : τ'.comp c = c.comp τ)
  (hfix : ∀ a : C, τ' (c a) - c a ∈ y') :
-- imply
  τ a - a ∈ Ideal.comap c y' := by
-- proof
  rw [Ideal.mem_comap, map_sub]
  have h := hfix a
  rwa [← RingHom.comp_apply, hcomm, RingHom.comp_apply] at h


-- created on 2026-10-03
