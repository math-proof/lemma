import Mathlib
import sympy.Basic

open CategoryTheory AlgebraicGeometry

/--
[AlgebraicGeometry_surjective_specMap_of_surjective_of_ker_le_nilradical](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_surjective_specMap_of_surjective_of_ker_le_nilradical.lean)
-/
@[path]
private lemma main
  {R S : Type u} [CommRing R] [CommRing S]
  {f : R →+* S}
-- given
  (hf : Function.Surjective f)
  (hker : RingHom.ker f ≤ nilradical R) :
-- imply
  Surjective (Spec.map (CommRingCat.ofHom f)) := by
-- proof
  have h := PrimeSpectrum.isHomeomorph_comap f (fun x => ⟨1, one_pos, by simpa using hf x⟩) hker
  exact ⟨fun x => by
    obtain ⟨y, hy⟩ := h.surjective x
    exact ⟨y, hy⟩⟩


-- created on 2026-10-05
