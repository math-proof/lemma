import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.AlgebraicGeometryI.code.IntersectionDimension
open Ideal


/--
[height_principal_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/IntersectionDimension.lean)
-/
@[path]
lemma height_principal_le_one
  [CommRing R]
  [IsNoetherianRing R]
  {f : R}
  {P : Ideal R}
  [P.IsPrime]
-- given
  (hP : P ∈ (Ideal.span ({f} : Set R)).minimalPrimes) :
-- imply
  P.height ≤ 1 := by
-- proof
  have : Submodule.IsPrincipal (Ideal.span ({f} : Set R)) := ⟨⟨f, by simp⟩⟩
  exact height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P hP

/--
[height_le_card_of_minimalPrimes_span](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/IntersectionDimension.lean)
-/
@[path]
lemma height_le_card_of_minimalPrimes_span
  [CommRing R]
  [IsNoetherianRing R]
  {P : Ideal R}
  {s : Finset R}
-- given
  (hP : P ∈ (Ideal.span (s : Set R)).minimalPrimes) :
-- imply
  P.height ≤ s.card :=
-- proof
  height_le_card_of_mem_minimalPrimes_span_finset hP

/--
[exists_generators_card_eq_height](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/IntersectionDimension.lean)
-/
@[path]
lemma exists_generators_card_eq_height
  [CommRing R]
  [IsNoetherianRing R]
  {P : Ideal R}
  [P.IsPrime] :
-- imply
  ∃ s : Finset R, P ∈ (Ideal.span (s : Set R)).minimalPrimes ∧ ↑s.card = P.height :=
-- proof
  Ideal.exists_finset_card_eq_height_of_isNoetherianRing P

/--
[dim_quotient_nonZeroDivisor_succ_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/IntersectionDimension.lean)
-/
@[path]
lemma dim_quotient_nonZeroDivisor_succ_le
  [CommRing R]
  {f : R}
-- given
  (hf : f ∈ nonZeroDivisors R) :
-- imply
  ringKrullDim (R ⧸ Ideal.span {f}) + 1 ≤ ringKrullDim R :=
-- proof
  ringKrullDim_quotient_succ_le_of_nonZeroDivisor hf

/--
[height_le_dim_quotient_principal_succ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/IntersectionDimension.lean)
-/
@[path]
lemma height_le_dim_quotient_principal_succ
  [CommRing R]
  [IsNoetherianRing R]
  {f : R}
  {P : Ideal R}
  [P.IsPrime]
-- given
  (hf : f ∈ P) :
-- imply
  ↑P.height ≤ ringKrullDim (R ⧸ Ideal.span {f}) + 1 :=
-- proof
  height_le_ringKrullDim_quotient_add_one hf

/--
[height_le_dim_quotient_add_encard](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/IntersectionDimension.lean)
-/
@[path]
lemma height_le_dim_quotient_add_encard
  [CommRing R]
  [IsNoetherianRing R]
  {P : Ideal R}
  [P.IsPrime]
  {s : Set R}
-- given
  (hs : s ⊆ ↑P) :
-- imply
  ↑P.height ≤ ringKrullDim (R ⧸ Ideal.span s) + ↑s.encard :=
-- proof
  Ideal.height_le_ringKrullDim_quotient_add_encard s hs

/--
[ringKrullDim_quotient_le_of_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/IntersectionDimension.lean)
-/
@[path]
lemma ringKrullDim_quotient_le_of_le
  [CommRing R]
  {I J : Ideal R}
-- given
  (h : I ≤ J) :
-- imply
  ringKrullDim (R ⧸ J) ≤ ringKrullDim (R ⧸ I) := by
-- proof
  apply ringKrullDim_le_of_surjective (Ideal.Quotient.factor h)
  intro x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨Ideal.Quotient.mk I r, rfl⟩


-- created on 2026-10-23
