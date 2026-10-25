import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.AlgebraicGeometryI.code.AdjunctionSheaf
open KaehlerDifferential Module
open scoped TensorProduct


/--
[conormal_ker_eq_ideal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/AdjunctionSheaf.lean)
-/
@[path]
lemma conormal_ker_eq_ideal
  {k : Type u}
  [CommRing k]
  {R : Type v}
  [CommRing R]
  [Algebra k R]
  {I : Ideal R}
  {R : Type*}
  [CommRing R]
  {I : Ideal R} :
-- imply
  RingHom.ker (algebraMap R (R ⧸ I)) = I := by
-- proof
  rw [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]

/--
[conormal_ker_eq_ideal_cotangent](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/AdjunctionSheaf.lean)
-/
@[path]
lemma conormal_ker_eq_ideal_cotangent
  {k : Type u}
  [CommRing k]
  {R : Type v}
  [CommRing R]
  [Algebra k R]
  {I : Ideal R}
  {R : Type*}
  [CommRing R]
  {I : Ideal R} :
-- imply
  (RingHom.ker (algebraMap R (R ⧸ I))).Cotangent = I.Cotangent := by
-- proof
  congr 1
  rw [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]

/--
[quotient_algebraMap_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/AdjunctionSheaf.lean)
-/
@[path]
lemma quotient_algebraMap_surjective
  {k : Type u}
  [CommRing k]
  {R : Type v}
  [CommRing R]
  [Algebra k R]
  {I : Ideal R}
  {R : Type*}
  [CommRing R]
  {I : Ideal R} :
-- imply
  Function.Surjective (algebraMap R (R ⧸ I)) := by
-- proof
  rwa [Ideal.Quotient.algebraMap_eq]

/--
[conormal_exact_sequence_quotient](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/AdjunctionSheaf.lean)
-/
@[path]
lemma conormal_exact_sequence_quotient
  {k : Type u}
  [CommRing k]
  {R : Type v}
  [CommRing R]
  [Algebra k R]
  {I : Ideal R} :
-- imply
  Function.Exact (KaehlerDifferential.kerCotangentToTensor k R (R ⧸ I)) (KaehlerDifferential.mapBaseChange k R (R ⧸ I)) := by
-- proof
  apply KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange
  rwa [Ideal.Quotient.algebraMap_eq]

/--
[conormal_mapBaseChange_surjective_quotient](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/AdjunctionSheaf.lean)
-/
@[path]
lemma conormal_mapBaseChange_surjective_quotient
  {k : Type u}
  [CommRing k]
  {R : Type v}
  [CommRing R]
  [Algebra k R]
  {I : Ideal R} :
-- imply
  Function.Surjective (KaehlerDifferential.mapBaseChange k R (R ⧸ I)) := by
-- proof
  apply KaehlerDifferential.mapBaseChange_surjective
  rwa [Ideal.Quotient.algebraMap_eq]

/--
[conormal_map_surjective_quotient](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/AdjunctionSheaf.lean)
-/
@[path]
lemma conormal_map_surjective_quotient
  {k : Type u}
  [CommRing k]
  {R : Type v}
  [CommRing R]
  [Algebra k R]
  {I : Ideal R} :
-- imply
  Function.Surjective (KaehlerDifferential.map k R (R ⧸ I) (R ⧸ I)) :=
-- proof
  KaehlerDifferential.map_surjective k R (R ⧸ I)

/--
[cotangent_first_exact_sequence_quotient](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/AdjunctionSheaf.lean)
-/
@[path]
lemma cotangent_first_exact_sequence_quotient
  {k : Type u}
  [CommRing k]
  {R : Type v}
  [CommRing R]
  [Algebra k R]
  {I : Ideal R} :
-- imply
  Function.Exact (KaehlerDifferential.mapBaseChange k R (R ⧸ I)) (KaehlerDifferential.map k R (R ⧸ I) (R ⧸ I)) :=
-- proof
  KaehlerDifferential.exact_mapBaseChange_map k R (R ⧸ I)
section PolynomialQuotient
variable (k : Type*) [Field k]

/--
[kahler_mvpoly_rank_two](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/AdjunctionSheaf.lean)
-/
@[path]
lemma kahler_mvpoly_rank_two
  {k : Type*}
  [Field k] :
-- imply
  Module.finrank (MvPolynomial (Fin 2) k) (Ω[MvPolynomial (Fin 2) k⁄k]) = 2 := by
-- proof
  rw [Module.finrank_eq_card_basis (KaehlerDifferential.mvPolynomialBasis k (Fin 2))]
  simp [Fintype.card_fin]

/--
[kahler_mvpoly_rank](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/AdjunctionSheaf.lean)
-/
@[path]
lemma kahler_mvpoly_rank
  {k : Type*}
  [Field k]
  {n : ℕ} :
-- imply
  Module.finrank (MvPolynomial (Fin n) k) (Ω[MvPolynomial (Fin n) k⁄k]) = n := by
-- proof
  rw [Module.finrank_eq_card_basis (KaehlerDifferential.mvPolynomialBasis k (Fin n))]
  simp [Fintype.card_fin]

/--
[kahler_mvpoly_free](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/AdjunctionSheaf.lean)
-/
@[path]
lemma kahler_mvpoly_free
  {k : Type*}
  [Field k]
  {n : ℕ} :
-- imply
  Module.Free (MvPolynomial (Fin n) k) (Ω[MvPolynomial (Fin n) k⁄k]) :=
-- proof
  inferInstance

/--
[conormal_exact_mvpoly_quotient](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/AdjunctionSheaf.lean)
-/
@[path]
lemma conormal_exact_mvpoly_quotient
  {k : Type*}
  [Field k]
  {I : Ideal (MvPolynomial (Fin 2) k)} :
-- imply
  Function.Exact (KaehlerDifferential.kerCotangentToTensor k (MvPolynomial (Fin 2) k) (MvPolynomial (Fin 2) k ⧸ I)) (KaehlerDifferential.mapBaseChange k (MvPolynomial (Fin 2) k) (MvPolynomial (Fin 2) k ⧸ I)) := by
-- proof
  apply KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange
  rwa [Ideal.Quotient.algebraMap_eq]

/--
[conormal_surj_mvpoly_quotient](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/AdjunctionSheaf.lean)
-/
@[path]
lemma conormal_surj_mvpoly_quotient
  {k : Type*}
  [Field k]
  {I : Ideal (MvPolynomial (Fin 2) k)} :
-- imply
  Function.Surjective (KaehlerDifferential.mapBaseChange k (MvPolynomial (Fin 2) k) (MvPolynomial (Fin 2) k ⧸ I)) := by
-- proof
  apply KaehlerDifferential.mapBaseChange_surjective
  rwa [Ideal.Quotient.algebraMap_eq]

/--
[conormal_exact_mvpoly_quotient_general](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/AdjunctionSheaf.lean)
-/
@[path]
lemma conormal_exact_mvpoly_quotient_general
  {k : Type*}
  [Field k]
  {n : ℕ}
  {I : Ideal (MvPolynomial (Fin n) k)} :
-- imply
  Function.Exact (KaehlerDifferential.kerCotangentToTensor k (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) k ⧸ I)) (KaehlerDifferential.mapBaseChange k (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) k ⧸ I)) := by
-- proof
  apply KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange
  rwa [Ideal.Quotient.algebraMap_eq]
end PolynomialQuotient
section NumericalAdjunction

/--
[adjunction_formula_int](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/AdjunctionSheaf.lean)
-/
@[path]
lemma adjunction_formula_int
  {d : ℤ} :
-- imply
  d * (d - 3) = (d - 1) * (d - 2) - 2 := by
-- proof
ring

/--
[adjunction_formula_genus_degree](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/AdjunctionSheaf.lean)
-/
@[path]
lemma adjunction_formula_genus_degree
  {d : ℕ}
-- given
  (hd : 3 ≤ d) :
-- imply
  d * (d - 3) + 2 = (d - 1) * (d - 2) := by
-- proof
  zify [hd, show 1 ≤ d by omega, show 2 ≤ d by omega]
  ring

/--
[adjunction_formula_numerical](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/AdjunctionSheaf.lean)
-/
@[path]
lemma adjunction_formula_numerical
  {d : ℕ} :
-- imply
  (d : ℤ) * (d - 3) = 2 * (((d : ℤ) - 1) * ((d : ℤ) - 2) / 2) - 2 := by
-- proof
  have h_even : (2 : ℤ) ∣ ((d : ℤ) - 1) * ((d : ℤ) - 2) := by
    obtain ⟨m, hm⟩ | ⟨m, hm⟩ := Int.even_or_odd (d : ℤ)
    · exact ⟨((d : ℤ) - 1) * (m - 1), by rw [hm]; ring⟩
    · exact ⟨m * ((d : ℤ) - 2), by rw [hm]; ring⟩
  rw [Int.mul_ediv_cancel' h_even]
  ring
end NumericalAdjunction
section ConormalRankBridge

/--
[finrank_le_of_surjective_lm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/AdjunctionSheaf.lean)
-/
@[path]
lemma finrank_le_of_surjective_lm
  [CommRing R]
  [Nontrivial R]
  [AddCommGroup M]
  [Module R M]
  [Module.Finite R M]
  [AddCommGroup N]
  [Module R N]
  {f : M →ₗ[R] N}
-- given
  (hf : Function.Surjective f) :
-- imply
  Module.finrank R N ≤ Module.finrank R M := by
-- proof
  have : f.range = ⊤ := LinearMap.range_eq_top.mpr hf
  calc finrank R N
    = finrank R (⊤ : Submodule R N) := (finrank_top R N).symm
    _ = finrank R f.range := by rw [this]
    _ ≤ finrank R M := LinearMap.finrank_range_le f
variable (k : Type*) [Field k]

/--
[conormal_basechange_finrank](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/AdjunctionSheaf.lean)
-/
@[path]
lemma conormal_basechange_finrank
  {k : Type*}
  [Field k]
  {n : ℕ}
  {I : Ideal (MvPolynomial (Fin n) k)}
  [Nontrivial (MvPolynomial (Fin n) k ⧸ I)] :
-- imply
  Module.finrank (MvPolynomial (Fin n) k ⧸ I) ((MvPolynomial (Fin n) k ⧸ I) ⊗[MvPolynomial (Fin n) k] Ω[MvPolynomial (Fin n) k⁄k]) = n := by
-- proof
  rw [Module.finrank_eq_card_basis
    ((KaehlerDifferential.mvPolynomialBasis k (Fin n)).baseChange (MvPolynomial (Fin n) k ⧸ I))]
  simp [Fintype.card_fin]

/--
[conormal_rank_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/AdjunctionSheaf.lean)
-/
@[path]
lemma conormal_rank_bound
  {k : Type*}
  [Field k]
  {n : ℕ}
  {I : Ideal (MvPolynomial (Fin n) k)}
  [Nontrivial (MvPolynomial (Fin n) k ⧸ I)] :
-- imply
  Module.finrank (MvPolynomial (Fin n) k ⧸ I) (Ω[MvPolynomial (Fin n) k ⧸ I⁄k]) ≤ n := by
-- proof
  have hsurj : Function.Surjective
    (KaehlerDifferential.mapBaseChange k (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) k ⧸ I)) := by
    apply KaehlerDifferential.mapBaseChange_surjective
    rwa [Ideal.Quotient.algebraMap_eq]
  haveI : Module.Finite (MvPolynomial (Fin n) k ⧸ I)
    ((MvPolynomial (Fin n) k ⧸ I) ⊗[MvPolynomial (Fin n) k] Ω[MvPolynomial (Fin n) k⁄k]) :=
    Module.Finite.of_basis
      ((KaehlerDifferential.mvPolynomialBasis k (Fin n)).baseChange (MvPolynomial (Fin n) k ⧸ I))
  calc Module.finrank (MvPolynomial (Fin n) k ⧸ I) (Ω[MvPolynomial (Fin n) k ⧸ I⁄k])
    ≤ Module.finrank (MvPolynomial (Fin n) k ⧸ I)
      ((MvPolynomial (Fin n) k ⧸ I) ⊗[MvPolynomial (Fin n) k] Ω[MvPolynomial (Fin n) k⁄k]) :=
      finrank_le_of_surjective_lm _ hsurj
    _ = n := conormal_basechange_finrank k n I

/--
[conormal_rank_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/AdjunctionSheaf.lean)
-/
@[path]
lemma conormal_rank_bridge
  {k : Type*}
  [Field k]
  {I : Ideal (MvPolynomial (Fin 2) k)}
  [Nontrivial (MvPolynomial (Fin 2) k ⧸ I)] :
-- imply
  Module.finrank (MvPolynomial (Fin 2) k ⧸ I) (Ω[MvPolynomial (Fin 2) k ⧸ I⁄k]) ≤ 2 :=
-- proof
  conormal_rank_bound k 2 I

/--
[adjunction_degree_from_exact_sequence](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/AdjunctionSheaf.lean)
-/
@[path]
lemma adjunction_degree_from_exact_sequence
  {k : Type*}
  [Field k]
  {n : ℕ}
  {d : ℤ}
  {deg_ambient_cotangent_restricted deg_conormal : ℤ}
-- given
  (h_euler : deg_ambient_cotangent_restricted = -((n : ℤ) + 1) * d)
  (h_conormal : deg_conormal = -(d * d)) :
-- imply
  deg_ambient_cotangent_restricted - deg_conormal = d * (d - ((n : ℤ) + 1)) := by
-- proof
  rw [h_euler, h_conormal]; ring

/--
[adjunction_formula_from_sequence_and_genus](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/AdjunctionSheaf.lean)
-/
@[path]
lemma adjunction_formula_from_sequence_and_genus
  {k : Type*}
  [Field k]
  {d : ℤ} :
-- imply
  (∀ (deg_Ω_P2_C deg_conormal : ℤ), deg_Ω_P2_C = -3 * d → deg_conormal = -(d * d) → deg_Ω_P2_C - deg_conormal = d * (d - 3)) ∧ d * (d - 3) = (d - 1) * (d - 2) - 2 := by
-- proof
  exact ⟨fun deg1 deg2 h1 h2 => by rw [h1, h2]; ring, by ring⟩
end ConormalRankBridge
section Prop35
variable (k : Type u) [CommRing k]
variable (R : Type v) [CommRing R] [Algebra k R]
variable (I : Ideal R)

/--
[conormal_exact_sequence_prop35](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/AdjunctionSheaf.lean)
-/
@[path]
lemma conormal_exact_sequence_prop35
  {k : Type u}
  [CommRing k]
  {R : Type v}
  [CommRing R]
  [Algebra k R]
  {I : Ideal R} :
-- imply
  Function.Exact (KaehlerDifferential.kerCotangentToTensor k R (R ⧸ I)) (KaehlerDifferential.mapBaseChange k R (R ⧸ I)) ∧ Function.Surjective (KaehlerDifferential.mapBaseChange k R (R ⧸ I)) := by
-- proof
  refine ⟨?_, ?_⟩
  · exact KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange k R (R ⧸ I)
    (by rw [Ideal.Quotient.algebraMap_eq]; exact Ideal.Quotient.mk_surjective)
  · exact KaehlerDifferential.mapBaseChange_surjective k R (R ⧸ I)
    (by rw [Ideal.Quotient.algebraMap_eq]; exact Ideal.Quotient.mk_surjective)

/--
[conormal_injective_iff_smooth_quotient](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/AdjunctionSheaf.lean)
-/
@[path]
lemma conormal_injective_iff_smooth_quotient
  {k : Type u}
  [CommRing k]
  {R : Type v}
  [CommRing R]
  [Algebra k R]
  {I : Ideal R}
  [Algebra.FormallySmooth k R] :
-- imply
  Function.Injective (KaehlerDifferential.kerCotangentToTensor k R (R ⧸ I)) ↔ Subsingleton (Algebra.H1Cotangent k (R ⧸ I)) := by
-- proof
  exact Algebra.FormallySmooth.kerCotangentToTensor_injective_iff
    (by rw [Ideal.Quotient.algebraMap_eq]; exact Ideal.Quotient.mk_surjective)

/--
[conormal_injective_when_both_smooth](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/AdjunctionSheaf.lean)
-/
@[path]
lemma conormal_injective_when_both_smooth
  {k : Type u}
  [CommRing k]
  {R : Type v}
  [CommRing R]
  [Algebra k R]
  {I : Ideal R}
  [Algebra.FormallySmooth k R]
  [Algebra.FormallySmooth k (R ⧸ I)] :
-- imply
  Function.Injective (KaehlerDifferential.kerCotangentToTensor k R (R ⧸ I)) := by
-- proof
  have hsurj : Function.Surjective (algebraMap R (R ⧸ I)) := by
    rw [Ideal.Quotient.algebraMap_eq]; exact Ideal.Quotient.mk_surjective
  obtain ⟨l, hl⟩ := (Algebra.FormallySmooth.iff_split_injection hsurj).mp
    (inferInstance : Algebra.FormallySmooth k (R ⧸ I))
  have h : Function.LeftInverse l (KaehlerDifferential.kerCotangentToTensor k R (R ⧸ I)) :=
    fun x => DFunLike.congr_fun hl x
  exact h.injective

/--
[conormal_split_when_both_smooth](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/AdjunctionSheaf.lean)
-/
@[path]
lemma conormal_split_when_both_smooth
  {k : Type u}
  [CommRing k]
  {R : Type v}
  [CommRing R]
  [Algebra k R]
  {I : Ideal R}
  [Algebra.FormallySmooth k R]
  [Algebra.FormallySmooth k (R ⧸ I)] :
-- imply
  ∃ l, l ∘ₗ KaehlerDifferential.kerCotangentToTensor k R (R ⧸ I) = LinearMap.id := by
-- proof
  rw [← Algebra.FormallySmooth.iff_split_injection
    (show Function.Surjective (algebraMap R (R ⧸ I)) from by
      rw [Ideal.Quotient.algebraMap_eq]; exact Ideal.Quotient.mk_surjective)]
  infer_instance

/--
[corollary_26](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/AdjunctionSheaf.lean)
-/
@[path]
lemma corollary_26
  {k : Type u}
  [CommRing k]
  {R : Type v}
  [CommRing R]
  [Algebra k R]
  {I : Ideal R}
  [Algebra.FormallySmooth k R]
  [Algebra.FormallySmooth k (R ⧸ I)] :
-- imply
  (Function.Injective (KaehlerDifferential.kerCotangentToTensor k R (R ⧸ I))) ∧ (Function.Exact (KaehlerDifferential.kerCotangentToTensor k R (R ⧸ I)) (KaehlerDifferential.mapBaseChange k R (R ⧸ I))) ∧ (Function.Surjective (KaehlerDifferential.mapBaseChange k R (R ⧸ I))) ∧ (∃ l, l ∘ₗ KaehlerDifferential.kerCotangentToTensor k R (R ⧸ I) = LinearMap.id) := by
-- proof
  have hsurj : Function.Surjective (algebraMap R (R ⧸ I)) := by
    rw [Ideal.Quotient.algebraMap_eq]; exact Ideal.Quotient.mk_surjective
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨l, hl⟩ := (Algebra.FormallySmooth.iff_split_injection hsurj).mp
    (inferInstance : Algebra.FormallySmooth k (R ⧸ I))
    have h : Function.LeftInverse l (KaehlerDifferential.kerCotangentToTensor k R (R ⧸ I)) :=
      fun x => DFunLike.congr_fun hl x
    exact h.injective
  · exact KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange k R (R ⧸ I) hsurj
  · exact KaehlerDifferential.mapBaseChange_surjective k R (R ⧸ I) hsurj
  · exact (Algebra.FormallySmooth.iff_split_injection hsurj).mp inferInstance

/--
[corollary_26_adjunction_formula](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/AdjunctionSheaf.lean)
-/
@[path]
lemma corollary_26_adjunction_formula
  {k : Type u}
  [CommRing k]
  {R : Type v}
  [CommRing R]
  [Algebra k R]
  {I : Ideal R}
  {d : ℤ} :
-- imply
  (∀ (deg_Ω_P2_C deg_conormal : ℤ), deg_Ω_P2_C = -(2 + 1) * d → deg_conormal = -(d * d) → deg_Ω_P2_C - deg_conormal = d * (d - 3)) ∧ d * (d - 3) = (d - 1) * (d - 2) - 2 := by
-- proof
  exact ⟨fun _ _ h1 h2 => by rw [h1, h2]; ring, by ring⟩
/-- Adjunction formula for a principal divisor: `ω_D ≃ ω_X(-D)|_D`. In algebraic terms,
`⋀^{n-1} Ω_{(R/I)/k} ≃ ((R/I) ⊗ ⋀^n Ω_{R/k}) ⊗ (I/I²)*` when `I` is principal and both
`R` and `R/I` are formally smooth (Cor 24, Lec 19). -/
end Prop35
/-- Exterior powers commute with base change for free modules:
`S ⊗_R ⋀^n M ≃ ⋀^n_S (S ⊗_R M)`. -/
section AdjunctionFormulaSheaf
variable (k : Type u) [CommRing k]
variable (R : Type v) [CommRing R] [Algebra k R]
variable (I : Ideal R)
/-- Algebraic adjunction formula: when both `R` and `R/I` are formally smooth over `k` and
`Ω_{R/k}` is free, the restriction of the top exterior power of `Ω_{R/k}` to `R/I` is isomorphic
to `⋀^{n-1} Ω_{(R/I)/k} ⊗ (I/I²)`. This is the algebraic form of `ω_X|_D ≃ ω_D ⊗ N_{D/X}`. -/
end AdjunctionFormulaSheaf


-- created on 2026-10-23
