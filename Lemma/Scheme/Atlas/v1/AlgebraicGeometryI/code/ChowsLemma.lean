import Mathlib
import sympy.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.ChowsLemma.Part2
open Polynomial ChowBlowup
open AlgebraicGeometry CategoryTheory Limits


/--
[algebraMap_reesAlgebra_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ChowsLemma.lean)
-/
@[path]
lemma algebraMap_reesAlgebra_injective
  {R : Type u}
  [CommRing R]
  {I : Ideal R} :
-- imply
  Function.Injective (algebraMap R (reesAlgebra I)) := by
-- proof
  intro a b hab
  have h : (algebraMap R (reesAlgebra I) a).1 = (algebraMap R (reesAlgebra I) b).1 :=
    congrArg Subtype.val hab
  exact Polynomial.C_injective h
end ChowStatement
section ChowsLemmaSchemeTheoretic
open AlgebraicGeometry CategoryTheory Limits

/--
[chows_lemma'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ChowsLemma.lean)
-/
@[path]
lemma chows_lemma'
  {S : Scheme.{u}}
  {X : Scheme.{u}}
  {f : X ⟶ S}
  [IsProper f]
  [AlgebraicGeometry.IsIntegral X] :
-- imply
  ∃ (X' : Scheme.{u}) (_ : IsProjectiveScheme X'), IsBirational X X' := by
-- proof
  obtain ⟨X_tilde, Y, hY_proj, g, hg_closed, hbir⟩ := second_proj_closed_immersion' f
  have hX_tilde_proj : IsProjectiveScheme X_tilde :=
    closed_subscheme_projective' g hg_closed hY_proj
  exact ⟨X_tilde, hX_tilde_proj, hbir⟩
end ChowsLemmaSchemeTheoretic

/--
[coeff_finset_sum_monomial](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ChowsLemma.lean)
-/
@[path]
private lemma coeff_finset_sum_monomial_eq
  [CommRing R]
  {s : Finset ℕ}
  {g : ℕ → R}
  {i : ℕ} :
-- imply
  (s.sum (fun j => Polynomial.monomial j (g j))).coeff i = if i ∈ s then g i else 0 := by
-- proof
  apply coeff_finset_sum_monomial i

/--
[mem_reesAlgebra_map](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ChowsLemma.lean)
-/
@[path]
private lemma mem_reesAlgebra_map_eq
  {R : Type u}
  {S : Type v}
  [CommRing R]
  [CommRing S]
  {f : R →+* S}
  {I : Ideal R}
  {p : R[X]}
-- given
  (hp : p ∈ reesAlgebra I) :
-- imply
  Polynomial.map f p ∈ reesAlgebra (I.map f) := by
-- proof
  apply ChowBlowup.mem_reesAlgebra_map f I p hp

/--
[symm_mem_ideal_pow_of_mem_map_pow](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ChowsLemma.lean)
-/
@[path]
private lemma symm_mem_ideal_pow_of_mem_map_pow_eq
  {R : Type u}
  {S : Type v}
  [CommRing R]
  [CommRing S]
  {e : R ≃+* S}
  {I : Ideal R}
  {i : ℕ}
  {s : S}
-- given
  (h : s ∈ (I.map (e : R →+* S)) ^ i) :
-- imply
  e.symm s ∈ I ^ i := by
-- proof
  apply ChowBlowup.symm_mem_ideal_pow_of_mem_map_pow e I i s h

/--
[mem_reesAlgebra_map_symm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ChowsLemma.lean)
-/
@[path]
private lemma mem_reesAlgebra_map_symm_eq
  {R : Type u}
  {S : Type v}
  [CommRing R]
  [CommRing S]
  {e : R ≃+* S}
  {I : Ideal R}
  {q : S[X]}
-- given
  (hq : q ∈ reesAlgebra (I.map (e : R →+* S))) :
-- imply
  Polynomial.map (e.symm : S →+* R) q ∈ reesAlgebra I := by
-- proof
  apply ChowBlowup.mem_reesAlgebra_map_symm e I q hq

/--
[reesAlgebra_comap_to_rees_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ChowsLemma.lean)
-/
@[path]
private lemma reesAlgebra_comap_to_rees_surjective_eq
  {R : Type u}
  {S : Type v}
  [CommRing R]
  [CommRing S]
  [CommRing R]
  [CommRing A]
  {f : R →+* A}
  {I : Ideal A}
-- given
  (hf : Function.Surjective f) :
-- imply
  Function.Surjective (reesAlgebra_comap_to_rees f I) := by
-- proof
  apply ChowBlowup.reesAlgebra_comap_to_rees_surjective f hf I


-- created on 2026-10-23
