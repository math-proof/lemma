import Mathlib
import sympy.Basic
import sympy.Algebra.Module.QuillenSuslin

open QuillenSuslin

/--
[qs_divByMonic_mul_monic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma divByMonic_mul_monic
  [CommRing R] [Nontrivial R]
-- given
  {b d : Polynomial R}
  (hb : b.Monic)
  (hd : d.Monic)
  (a : Polynomial R) :
-- imply
  Polynomial.divByMonic (d * a) (d * b) = Polynomial.divByMonic a b := by
-- proof
  apply qs_divByMonic_mul_monic a hb hd


/--
[qs_divByMonic_eq_of_localization_rel](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma divByMonic_eq_of_localization_rel
  [CommRing R]
  [Nontrivial R]
  {a c : Polynomial R}
  {b d : qsMonicSubmonoid R}
-- given
  (h : Localization.r (qsMonicSubmonoid R) (a, b) (c, d)) :
-- imply
  Polynomial.divByMonic a (b : Polynomial R) = Polynomial.divByMonic c (d : Polynomial R) := by
-- proof
  apply qs_divByMonic_eq_of_localization_rel h


/--
[qsPolynomialPartFun_mk](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma polynomialPartFun_mk
  [CommRing R] [Nontrivial R]
-- given
  (a : Polynomial R)
  (b : qsMonicSubmonoid R) :
-- imply
  qsPolynomialPartFun (Localization.mk a b) = Polynomial.divByMonic a (b : Polynomial R) := by
-- proof
  apply qsPolynomialPartFun_mk a b


/--
[qsPolynomialPartFun_add](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma polynomialPartFun_add
  [CommRing R] [Nontrivial R]
-- given
  (x y : Localization (qsMonicSubmonoid R)) :
-- imply
  qsPolynomialPartFun (x + y) = qsPolynomialPartFun x + qsPolynomialPartFun y := by
-- proof
  apply qsPolynomialPartFun_add x y


/--
[qsPolynomialPartFun_smul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma polynomialPartFun_smul
  [CommRing R] [Nontrivial R]
-- given
  (r : R)
  (x : Localization (qsMonicSubmonoid R)) :
-- imply
  qsPolynomialPartFun (r • x) = r • qsPolynomialPartFun x := by
-- proof
  apply qsPolynomialPartFun_smul r x


/--
[qsPolynomialPart_algebraMap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma polynomialPart_algebraMap
  [CommRing R] [Nontrivial R]
-- given
  (p : Polynomial R) :
-- imply
  qsPolynomialPart R (algebraMap (Polynomial R) (Localization (qsMonicSubmonoid R)) p) = p := by
-- proof
  apply qsPolynomialPart_algebraMap p


/--
[qs_exists_monic_lift](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma exists_monic_lift
  [CommRing R] [CommRing S] [Nontrivial R] [Nontrivial S]
-- given
  (f : R →+* S)
  {p : Polynomial S}
  (hf : Function.Surjective f)
  (hp : p.Monic) :
-- imply
  ∃ q : Polynomial R, q.Monic ∧ q.map f = p := by
-- proof
  apply qs_exists_monic_lift f hf hp


/--
[qs_map_monicSubmonoid_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma map_monicSubmonoid_eq
  [CommRing R] [CommRing S] [Nontrivial R] [Nontrivial S]
-- given
  (f : R →+* S)
  (hf : Function.Surjective f) :
-- imply
  (qsMonicSubmonoid R).map (Polynomial.mapRingHom f) = qsMonicSubmonoid S := by
-- proof
  apply qs_map_monicSubmonoid_eq f hf


/--
[qs_monicLocalization_isFractionRing](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma monicLocalization_isFractionRing
  [Field k] :
-- imply
  IsFractionRing (Polynomial k) (Localization (qsMonicSubmonoid k)) := by
-- proof
  apply qs_monicLocalization_isFractionRing k


/--
[qs_nonzero_polynomial_maps_to_unit](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma nonzero_polynomial_maps_to_unit
  [Field k] [CommRing A] [Nontrivial A]
-- given
  {p : Polynomial k}
  (hp : p ≠ 0)
  (f : k →+* A) :
-- imply
  IsUnit (((algebraMap (Polynomial A) (Localization (qsMonicSubmonoid A))).comp (Polynomial.mapRingHom f)) p) := by
-- proof
  apply qs_nonzero_polynomial_maps_to_unit f hp


/--
[qsFractionToMonicLocalization_algebraMap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma fractionToMonicLocalization_algebraMap
  [Field k] [CommRing A] [Nontrivial A]
-- given
  (f : k →+* A)
  (p : Polynomial k) :
-- imply
  qsFractionToMonicLocalization k A f (algebraMap (Polynomial k) (FractionRing (Polynomial k)) p) = algebraMap (Polynomial A) (Localization (qsMonicSubmonoid A)) (p.map f) := by
-- proof
  apply qsFractionToMonicLocalization_algebraMap k A f p


/--
[qs_genericSpecialization_comp_genericMap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma genericSpecialization_comp_genericMap
  [Field k] [CommRing A] [Nontrivial A]
-- given
  (n : ℕ)
  (f : MvPolynomial (Fin n) k →+* A) :
-- imply
  (qsGenericSpecialization k n A f).comp (qsGenericMap k n) = (algebraMap (Polynomial A) (Localization (qsMonicSubmonoid A))).comp (Polynomial.mapRingHom f) := by
-- proof
  apply qs_genericSpecialization_comp_genericMap k n A f


/--
[qsResidueMonicMap_algebraMap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma residueMonicMap_algebraMap
  [CommRing R] [IsLocalRing R]
-- given
  (p : Polynomial R) :
-- imply
  qsResidueMonicMap R (algebraMap (Polynomial R) (Localization (qsMonicSubmonoid R)) p) = algebraMap (Polynomial (IsLocalRing.ResidueField R)) (Localization (qsMonicSubmonoid (IsLocalRing.ResidueField R))) (p.map (IsLocalRing.residue R)) := by
-- proof
  apply qsResidueMonicMap_algebraMap R p


/--
[qsResidueMonicMap_mk](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma residueMonicMap_mk
  [CommRing R] [IsLocalRing R]
-- given
  (p : Polynomial R)
  (s : qsMonicSubmonoid R) :
-- imply
  qsResidueMonicMap R (Localization.mk p s) = Localization.mk (p.map (IsLocalRing.residue R)) (⟨(s : Polynomial R).map (IsLocalRing.residue R), s.property.map (IsLocalRing.residue R)⟩ : qsMonicSubmonoid (IsLocalRing.ResidueField R)) := by
-- proof
  apply qsResidueMonicMap_mk R p s


/--
[qsPolynomialPart_map_residue](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma polynomialPart_map_residue
  [CommRing R] [IsLocalRing R]
-- given
  (z : Localization (qsMonicSubmonoid R)) :
-- imply
  (qsPolynomialPart R z).map (IsLocalRing.residue R) = qsPolynomialPart (IsLocalRing.ResidueField R) (qsResidueMonicMap R z) := by
-- proof
  apply qsPolynomialPart_map_residue R z


/--
[qsMatrixPolynomialPart_transpose](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma matrixPolynomialPart_transpose
  [CommRing R] [Nontrivial R]
-- given
  (A : Matrix ι κ (Localization (qsMonicSubmonoid R))) :
-- imply
  qsMatrixPolynomialPart R A.transpose = (qsMatrixPolynomialPart R A).transpose := by
-- proof
  apply qsMatrixPolynomialPart_transpose R A


/--
[qsMatrixPolynomialPart_algebraMap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma matrixPolynomialPart_algebraMap
  [CommRing R] [Nontrivial R]
-- given
  (A : Matrix ι κ (Polynomial R)) :
-- imply
  qsMatrixPolynomialPart R (A.map (algebraMap (Polynomial R) (Localization (qsMonicSubmonoid R)))) = A := by
-- proof
  apply qsMatrixPolynomialPart_algebraMap A


/--
[qsMatrixPolynomialPart_map_residue](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma matrixPolynomialPart_map_residue
  [CommRing R] [IsLocalRing R]
-- given
  (A : Matrix ι κ (Localization (qsMonicSubmonoid R)))
  (C : Matrix ι κ (Polynomial (IsLocalRing.ResidueField R)))
  (hAC : A.map (qsResidueMonicMap R) =
      C.map (algebraMap (Polynomial (IsLocalRing.ResidueField R))
        (Localization (qsMonicSubmonoid (IsLocalRing.ResidueField R))))) :
-- imply
  (qsMatrixPolynomialPart R A).map (Polynomial.mapRingHom (IsLocalRing.residue R)) = C := by
-- proof
  apply qsMatrixPolynomialPart_map_residue R A C hAC


/--
[qsPolynomialPart_mul_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma polynomialPart_mul_eq_zero
  [CommRing R] [Nontrivial R]
  {x y : Localization (qsMonicSubmonoid R)}
-- given
  (hx : qsPolynomialPart R x = 0)
  (hy : qsPolynomialPart R y = 0) :
-- imply
  qsPolynomialPart R (x * y) = 0 := by
-- proof
  apply qsPolynomialPart_mul_eq_zero hx hy


/--
[qs_isUnit_one_add_of_polynomialPart_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma isUnit_one_add_of_polynomialPart_eq_zero
  [CommRing R] [Nontrivial R]
-- given
  (z : Localization (qsMonicSubmonoid R))
  (hz : qsPolynomialPart R z = 0) :
-- imply
  IsUnit (1 + z) := by
-- proof
  apply qs_isUnit_one_add_of_polynomialPart_eq_zero z hz


/--
[qsPolynomialPart_C_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma polynomialPart_C_mul
  [CommRing R] [Nontrivial R]
-- given
  (r : R)
  (z : Localization (qsMonicSubmonoid R)) :
-- imply
  qsPolynomialPart R (algebraMap (Polynomial R) (Localization (qsMonicSubmonoid R)) (Polynomial.C r) * z) = r • qsPolynomialPart R z := by
-- proof
  apply qsPolynomialPart_C_mul r z


/--
[qsPolynomialPart_mul_of_constant_parts](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma polynomialPart_mul_of_constant_parts
  [CommRing R]
  [Nontrivial R]
  {x y : Localization (qsMonicSubmonoid R)}
  {r s : R}
-- given
  (hx : qsPolynomialPart R x = Polynomial.C r)
  (hy : qsPolynomialPart R y = Polynomial.C s) :
-- imply
  qsPolynomialPart R (x * y) = Polynomial.C (r * s) := by
-- proof
  apply qsPolynomialPart_mul_of_constant_parts hx hy


/--
[qsPolynomialPart_prod_of_constant_parts](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma polynomialPart_prod_of_constant_parts
  [CommRing R] [Nontrivial R]
-- given
  (t : Finset α)
  (f : α → Localization (qsMonicSubmonoid R))
  (g : α → R)
  (h : ∀ i ∈ t, qsPolynomialPart R (f i) = Polynomial.C (g i)) :
-- imply
  qsPolynomialPart R (∏ i ∈ t, f i) = Polynomial.C (∏ i ∈ t, g i) := by
-- proof
  apply qsPolynomialPart_prod_of_constant_parts t f g h


/--
[qsPolynomialPart_det_of_constant_parts](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma polynomialPart_det_of_constant_parts
  [CommRing R] [Nontrivial R] [Fintype ι] [DecidableEq ι]
-- given
  (H : Matrix ι ι (Localization (qsMonicSubmonoid R)))
  (M : Matrix ι ι R)
  (h : ∀ i j, qsPolynomialPart R (H i j) = Polynomial.C (M i j)) :
-- imply
  qsPolynomialPart R H.det = Polynomial.C M.det := by
-- proof
  apply qsPolynomialPart_det_of_constant_parts H M h


/--
[qs_isUnit_det_of_matrixPolynomialPart_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma isUnit_det_of_matrixPolynomialPart_eq_one
  [CommRing R] [Nontrivial R] [Fintype ι] [DecidableEq ι]
-- given
  (H : Matrix ι ι (Localization (qsMonicSubmonoid R)))
  (hH : ∀ i j, qsPolynomialPart R (H i j) =
      (1 : Matrix ι ι (Polynomial R)) i j) :
-- imply
  IsUnit H.det := by
-- proof
  apply qs_isUnit_det_of_matrixPolynomialPart_eq_one H hH


/--
[qsHorrocksMap_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma horrocksMap_apply
  [CommRing R] [Nontrivial R] [Fintype ι]
-- given
  (A : Matrix ι κ (Localization (qsMonicSubmonoid R)))
  (F : Matrix κ ι (Polynomial R)) :
-- imply
  qsHorrocksMap R A F = qsMatrixPolynomialPart R (F.map (algebraMap (Polynomial R) (Localization (qsMonicSubmonoid R))) * A) := by
-- proof
  apply qsHorrocksMap_apply R A F


/--
[qs_exists_monic_matrix_multiple](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma exists_monic_matrix_multiple
  [CommRing R] [Nontrivial R] [Finite ι] [Finite κ]
-- given
  (B : Matrix ι κ (Localization (qsMonicSubmonoid R))) :
-- imply
  ∃ h : Polynomial R, h.Monic ∧ ∃ B₀ : Matrix ι κ (Polynomial R), B₀.map (algebraMap (Polynomial R) (Localization (qsMonicSubmonoid R))) = (algebraMap (Polynomial R) (Localization (qsMonicSubmonoid R)) h) • B := by
-- proof
  apply qs_exists_monic_matrix_multiple R B


/--
[qs_horrocks_multiple_mem_range](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma horrocks_multiple_mem_range
  [CommRing R] [Nontrivial R] [Fintype ι] [Finite κ] [DecidableEq κ]
-- given
  (A : Matrix ι κ (Localization (qsMonicSubmonoid R)))
  (B : Matrix κ ι (Localization (qsMonicSubmonoid R)))
  (B₀ : Matrix κ ι (Polynomial R))
  (h : Polynomial R)
  (hBA : B * A = 1)
  (hB₀ : B₀.map (algebraMap (Polynomial R)
      (Localization (qsMonicSubmonoid R))) =
      (algebraMap (Polynomial R)
        (Localization (qsMonicSubmonoid R)) h) • B)
  (G : Matrix κ κ (Polynomial R)) :
-- imply
  h • G ∈ LinearMap.range (qsHorrocksMap R A) := by
-- proof
  apply qs_horrocks_multiple_mem_range R A B hBA h B₀ hB₀ G


/--
[qs_matrix_mem_maximal_smul_of_map_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma matrix_mem_maximal_smul_of_map_eq_zero
  [CommRing R] [IsLocalRing R] [Finite ι] [Finite κ]
-- given
  (P : Matrix ι κ (Polynomial R))
  (hP : P.map (Polynomial.mapRingHom (IsLocalRing.residue R)) = 0) :
-- imply
  P ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R (Matrix ι κ (Polynomial R))) := by
-- proof
  apply qs_matrix_mem_maximal_smul_of_map_eq_zero R P hP


/--
[qs_quotient_finite_of_monic_smul_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma quotient_finite_of_monic_smul_mem
  [CommRing R] [Nontrivial R] [Finite κ]
-- given
  (N : Submodule R (Matrix κ κ (Polynomial R)))
  (h : Polynomial R)
  (hh : h.Monic)
  (hN : ∀ G : Matrix κ κ (Polynomial R), h • G ∈ N) :
-- imply
  Module.Finite R (Matrix κ κ (Polynomial R) ⧸ N) := by
-- proof
  apply qs_quotient_finite_of_monic_smul_mem R N h hh hN


/--
[qs_horrocks_range_sup_maximal_eq_top](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma horrocks_range_sup_maximal_eq_top
  [CommRing R] [IsLocalRing R] [Fintype ι] [Fintype κ] [DecidableEq κ]
-- given
  (A : Matrix ι κ (Localization (qsMonicSubmonoid R)))
  (B : Matrix κ ι (Localization (qsMonicSubmonoid R)))
  (hBA : B * A = 1)
  (hA : ∃ C : Matrix ι κ (Polynomial (IsLocalRing.ResidueField R)),
      A.map (qsResidueMonicMap R) =
        C.map (algebraMap (Polynomial (IsLocalRing.ResidueField R))
          (Localization (qsMonicSubmonoid (IsLocalRing.ResidueField R)))))
  (hB : ∃ D : Matrix κ ι (Polynomial (IsLocalRing.ResidueField R)),
      B.map (qsResidueMonicMap R) =
        D.map (algebraMap (Polynomial (IsLocalRing.ResidueField R))
          (Localization (qsMonicSubmonoid (IsLocalRing.ResidueField R))))) :
-- imply
  LinearMap.range (qsHorrocksMap R A) ⊔ IsLocalRing.maximalIdeal R • (⊤ : Submodule R (Matrix κ κ (Polynomial R))) = ⊤ := by
-- proof
  apply qs_horrocks_range_sup_maximal_eq_top R A B hBA hA hB


/--
[qs_horrocks_map_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma horrocks_map_surjective
  [CommRing R] [IsLocalRing R] [Fintype ι] [Finite κ] [DecidableEq κ]
-- given
  (A : Matrix ι κ (Localization (qsMonicSubmonoid R)))
  (B : Matrix κ ι (Localization (qsMonicSubmonoid R)))
  (hBA : B * A = 1)
  (hA : ∃ C : Matrix ι κ (Polynomial (IsLocalRing.ResidueField R)),
      A.map (qsResidueMonicMap R) =
        C.map (algebraMap (Polynomial (IsLocalRing.ResidueField R))
          (Localization (qsMonicSubmonoid (IsLocalRing.ResidueField R)))))
  (hB : ∃ D : Matrix κ ι (Polynomial (IsLocalRing.ResidueField R)),
      B.map (qsResidueMonicMap R) =
        D.map (algebraMap (Polynomial (IsLocalRing.ResidueField R))
          (Localization (qsMonicSubmonoid (IsLocalRing.ResidueField R))))) :
-- imply
  Function.Surjective (qsHorrocksMap R A) := by
-- proof
  apply qs_horrocks_map_surjective R A B hBA hA hB


/--
[qs_lift_invertible_matrix](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma lift_invertible_matrix
  [CommRing A] [Field K] [Fintype ι] [DecidableEq ι]
-- given
  (f : A →+* K)
  (M : Matrix ι ι K)
  (hlift : ∀ x : K, x ≠ 0 → ∃ u : Aˣ, f u = x)
  (hM : M.det ≠ 0) :
-- imply
  ∃ U : Matrix ι ι A, IsUnit U.det ∧ U.map f = M := by
-- proof
  apply qs_lift_invertible_matrix f hlift M hM


/--
[qsResidueMonicMap_lifts_unit](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma residueMonicMap_lifts_unit
  [CommRing R] [IsLocalRing R]
-- given
  (z : Localization (qsMonicSubmonoid (IsLocalRing.ResidueField R)))
  (hz : z ≠ 0) :
-- imply
  ∃ u : (Localization (qsMonicSubmonoid R))ˣ, qsResidueMonicMap R u = z := by
-- proof
  apply qsResidueMonicMap_lifts_unit R z hz


/--
[qs_lift_residue_invertible_matrix](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma lift_residue_invertible_matrix
  [CommRing R] [IsLocalRing R] [Fintype ι] [DecidableEq ι]
-- given
  (M : Matrix ι ι
      (Localization (qsMonicSubmonoid (IsLocalRing.ResidueField R))))
  (hM : M.det ≠ 0) :
-- imply
  ∃ U : Matrix ι ι (Localization (qsMonicSubmonoid R)), IsUnit U.det ∧ U.map (qsResidueMonicMap R) = M := by
-- proof
  apply qs_lift_residue_invertible_matrix R M hM


/--
[qsMatrixEquiv.refl](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma matrixEquiv_refl
  [CommRing R] [Fintype i]
  {E : Matrix i i R}
-- given
  (hE : E * E = E) :
-- imply
  qsMatrixEquiv E E := by
-- proof
  apply qsMatrixEquiv.refl hE


/--
[qsShear_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma shear_zero
  [CommRing R] :
-- imply
  qsShear (0 : R) = (Polynomial.C : Polynomial R →+* Polynomial (Polynomial R)) := by
-- proof
  apply qsShear_zero


/--
[qsShiftX_comp_shear](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma shiftX_comp_shear
  [CommRing R]
-- given
  (j j' : R) :
-- imply
  (qsShiftX j').comp (qsShear j) = qsShear (j + j') := by
-- proof
  apply qsShiftX_comp_shear j j'


/--
[qsShiftX_comp_C](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma shiftX_comp_C
  [CommRing R]
-- given
  (j : R) :
-- imply
  (qsShiftX j).comp (Polynomial.C : Polynomial R →+* Polynomial (Polynomial R)) = qsShear j := by
-- proof
  apply qsShiftX_comp_C j


/--
[qsScaleY_comp_shear](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma scaleY_comp_shear
  [CommRing R]
-- given
  (r j : R) :
-- imply
  (qsScaleY r).comp (qsShear j) = qsShear (r * j) := by
-- proof
  apply qsScaleY_comp_shear r j


/--
[qsScaleY_comp_C](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma scaleY_comp_C
  [CommRing R]
-- given
  (r : R) :
-- imply
  (qsScaleY r).comp (Polynomial.C : Polynomial R →+* Polynomial (Polynomial R)) = (Polynomial.C : Polynomial R →+* Polynomial (Polynomial R)) := by
-- proof
  apply qsScaleY_comp_C r


/--
[qs_scale_shear_map](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma scale_shear_map
  [CommRing R] [CommRing S]
-- given
  (f : R →+* S)
  (r : R) :
-- imply
  (qsScaleY (f r)).comp ((qsShear (1 : S)).comp (Polynomial.mapRingHom f)) = (Polynomial.mapRingHom (Polynomial.mapRingHom f)).comp (qsShear r) := by
-- proof
  apply qs_scale_shear_map f r


/--
[qsEvalXY_comp_shear_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma evalXY_comp_shear_one
  [CommRing R] :
-- imply
  (qsEvalXY : Polynomial (Polynomial R) →+* Polynomial R).comp (qsShear (1 : R)) = RingHom.id (Polynomial R) := by
-- proof
  apply qsEvalXY_comp_shear_one


/--
[qsEvalXY_comp_C](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma evalXY_comp_C
  [CommRing R] :
-- imply
  (qsEvalXY : Polynomial (Polynomial R) →+* Polynomial R).comp Polynomial.C = qsConstantAtZero := by
-- proof
  apply qsEvalXY_comp_C


/--
[qsMatrixEquiv.symm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma matrixEquiv_symm
  [CommRing R]
  [Fintype ι] [Fintype κ]
  {E : Matrix ι ι R}
  {F : Matrix κ κ R}
-- given
  (h : qsMatrixEquiv E F) :
-- imply
  qsMatrixEquiv F E := by
-- proof
  apply qsMatrixEquiv.symm h


/--
[qsMatrixEquiv.reindex_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma matrixEquiv_reindex_one
  [CommRing R] [Fintype ι] [Fintype κ] [Fintype η]
  [DecidableEq κ] [DecidableEq η]
  {E : Matrix ι ι R}
-- given
  (h : qsMatrixEquiv E (1 : Matrix κ κ R))
  (e : η ≃ κ) :
-- imply
  qsMatrixEquiv E (1 : Matrix η η R) := by
-- proof
  apply qsMatrixEquiv.reindex_one h e


/--
[qsMatrixEquiv.map](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma matrixEquiv_map
  [CommRing R] [CommRing S]
  [Fintype ι] [Fintype κ]
  {E : Matrix ι ι R}
  {F : Matrix κ κ R}
-- given
  (h : qsMatrixEquiv E F)
  (f : R →+* S) :
-- imply
  qsMatrixEquiv (E.map f) (F.map f) := by
-- proof
  apply qsMatrixEquiv.map h f


/--
[qs_transition_one_of_equal_after](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma transition_one_of_equal_after
  [CommRing R] [CommRing S] [CommRing T] [Fintype i] [Fintype k]
  [DecidableEq k]
  {E : Matrix i i R}
-- given
  (g₁ g₂ : R →+* S)
  (e : S →+* T)
  (he : e.comp g₁ = e.comp g₂)
  (h : qsMatrixEquiv E (1 : Matrix k k R)) :
-- imply
  ∃ C D : Matrix i i S, C * D = E.map g₁ ∧ D * C = E.map g₂ ∧ C.map e = E.map (e.comp g₁) ∧ D.map e = E.map (e.comp g₁) := by
-- proof
  apply qs_transition_one_of_equal_after h g₁ g₂ e he


/--
[qsMatrixEquiv.trans](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma matrixEquiv_trans
  [CommRing R]
  [Fintype ι] [Fintype κ] [Fintype η]
  {E : Matrix ι ι R}
  {F : Matrix κ κ R}
  {G : Matrix η η R}
-- given
  (hEF : qsMatrixEquiv E F)
  (hFG : qsMatrixEquiv F G)
  (hE : E * E = E)
  (hG : G * G = G) :
-- imply
  qsMatrixEquiv E G := by
-- proof
  apply qsMatrixEquiv.trans hEF hFG hE hG


/--
[qs_idempotent_map](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma idempotent_map
  [CommRing R] [CommRing S] [Fintype i]
  {E : Matrix i i R}
-- given
  (hE : E * E = E)
  (f : R →+* S) :
-- imply
  E.map f * E.map f = E.map f := by
-- proof
  apply qs_idempotent_map hE f


/--
[qs_patching_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma patching_zero
  [CommRing R] [Fintype i]
  {E : Matrix i i (Polynomial R)}
-- given
  (hE : E * E = E) :
-- imply
  qsMatrixEquiv (E.map (qsShear (0 : R))) (E.map (Polynomial.C : Polynomial R →+* Polynomial (Polynomial R))) := by
-- proof
  apply qs_patching_zero hE


/--
[qs_patching_add](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma patching_add
  [CommRing R] [Fintype i]
  {E : Matrix i i (Polynomial R)}
-- given
  {j j' : R}
  (hE : E * E = E)
  (hj : qsMatrixEquiv (E.map (qsShear j))
      (E.map (Polynomial.C : Polynomial R →+* Polynomial (Polynomial R))))
  (hj' : qsMatrixEquiv (E.map (qsShear j'))
      (E.map (Polynomial.C : Polynomial R →+* Polynomial (Polynomial R)))) :
-- imply
  qsMatrixEquiv (E.map (qsShear (j + j'))) (E.map (Polynomial.C : Polynomial R →+* Polynomial (Polynomial R))) := by
-- proof
  apply qs_patching_add hE hj hj'


/--
[qs_patching_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma patching_mul
  [CommRing R] [Fintype i]
  {E : Matrix i i (Polynomial R)}
  {j : R}
-- given
  (r : R)
  (hj : qsMatrixEquiv (E.map (qsShear j))
      (E.map (Polynomial.C : Polynomial R →+* Polynomial (Polynomial R)))) :
-- imply
  qsMatrixEquiv (E.map (qsShear (r * j))) (E.map (Polynomial.C : Polynomial R →+* Polynomial (Polynomial R))) := by
-- proof
  apply qs_patching_mul hj r


/--
[qs_exists_lifts_after_scale](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma exists_lifts_after_scale
  [CommRing R] [CommRing S] [Algebra R S]
  {M : Submonoid R} [IsLocalization M S]
  {a : Type*} [Finite a]
-- given
  (p : a → Polynomial S)
  (hzero : ∀ i, (p i).coeff 0 = 0) :
-- imply
  ∃ b : M, ∀ i, ∃ q : Polynomial R, q.map (algebraMap R S) = (p i).comp (Polynomial.C (algebraMap R S b) * Polynomial.X) := by
-- proof
  apply qs_exists_lifts_after_scale p hzero


/--
[qs_constantCoeff_comp_shear_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma constantCoeff_comp_shear_one
  [CommRing R] :
-- imply
  (Polynomial.constantCoeff : Polynomial (Polynomial R) →+* Polynomial R).comp (qsShear (1 : R)) = (Polynomial.constantCoeff : Polynomial (Polynomial R) →+* Polynomial R).comp Polynomial.C := by
-- proof
  apply qs_constantCoeff_comp_shear_one


/--
[qs_constantCoeff_comp_shear_one_eq_id](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma constantCoeff_comp_shear_one_eq_id
  [CommRing R] :
-- imply
  (Polynomial.constantCoeff : Polynomial (Polynomial R) →+* Polynomial R).comp (qsShear (1 : R)) = RingHom.id (Polynomial R) := by
-- proof
  apply qs_constantCoeff_comp_shear_one_eq_id


/--
[qs_exists_transition_with_zero_constant](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma exists_transition_with_zero_constant
  [CommRing R] [Fintype i] [Fintype k]
  [DecidableEq k]
  {E : Matrix i i (Polynomial R)}
-- given
  (h : qsMatrixEquiv E (1 : Matrix k k (Polynomial R))) :
-- imply
  ∃ C D : Matrix i i (Polynomial (Polynomial R)), C * D = E.map (qsShear (1 : R)) ∧ D * C = E.map (Polynomial.C : Polynomial R →+* Polynomial (Polynomial R)) ∧ (∀ x y, (C x y - Polynomial.C (E x y)).coeff 0 = 0) ∧ ∀ x y, (D x y - Polynomial.C (E x y)).coeff 0 = 0 := by
-- proof
  apply qs_exists_transition_with_zero_constant h


/--
[qs_patching_member_of_localization](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma patching_member_of_localization
  [CommRing R] [CommRing S] [Algebra R S]
  [Fintype i] [Fintype k] [DecidableEq k]
  {M : Submonoid R} [IsLocalization M S]
-- given
  (E : Matrix i i (Polynomial R))
  (hM : M ≤ nonZeroDivisors R)
  (hE : E * E = E)
  (hlocal : qsMatrixEquiv
      (E.map (Polynomial.mapRingHom (algebraMap R S)))
      (1 : Matrix k k (Polynomial S))) :
-- imply
  ∃ r : M, (r : R) ∈ qsPatchingIdeal E hE := by
-- proof
  apply qs_patching_member_of_localization hM E hE hlocal


/--
[qs_quillen_patching](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma quillen_patching
  [CommRing R] [IsDomain R] [Fintype i]
-- given
  (E : Matrix i i (Polynomial R))
  (hE : E * E = E)
  (hlocal : ∀ (m : Ideal R) (hm : m.IsMaximal),
      let _ : m.IsPrime := hm.isPrime
      ∃ n : ℕ, qsMatrixEquiv
        (E.map (Polynomial.mapRingHom (algebraMap R (Localization.AtPrime m))))
        (1 : Matrix (Fin n) (Fin n) (Polynomial (Localization.AtPrime m)))) :
-- imply
  qsMatrixEquiv E (E.map (qsConstantAtZero : Polynomial R →+* Polynomial R)) := by
-- proof
  apply qs_quillen_patching E hE hlocal


/--
[qs_range_projective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma range_projective
  [CommRing R] [Fintype ι]
-- given
  (E : Matrix ι ι R)
  (hE : E * E = E) :
-- imply
  Module.Projective R (LinearMap.range E.mulVecLin) := by
-- proof
  apply qs_range_projective E hE


/--
[qs_range_finite](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma range_finite
  [CommRing R] [Fintype ι]
-- given
  (E : Matrix ι ι R) :
-- imply
  Module.Finite R (LinearMap.range E.mulVecLin) := by
-- proof
  apply qs_range_finite E


/--
[qs_mulVec_eq_self_of_mem_range](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma mulVec_eq_self_of_mem_range
  [CommRing R] [Fintype ι]
  {E : Matrix ι ι R}
-- given
  {x : ι → R}
  (hE : E * E = E)
  (hx : x ∈ LinearMap.range E.mulVecLin) :
-- imply
  E.mulVecLin x = x := by
-- proof
  apply qs_mulVec_eq_self_of_mem_range hE hx


/--
[qs_equiv_one_of_free_range](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma equiv_one_of_free_range
  {R : Type u} [CommRing R]
  {ι : Type v} [Fintype ι]
-- given
  (E : Matrix ι ι R)
  (hE : E * E = E)
  [Module.Free R (LinearMap.range E.mulVecLin)]
  [Module.Finite R (LinearMap.range E.mulVecLin)] :
-- imply
  ∃ (κ : Type (max u v)) (_ : Fintype κ) (_ : DecidableEq κ), qsMatrixEquiv E (1 : Matrix κ κ R) := by
-- proof
  apply qs_equiv_one_of_free_range E hE


/--
[qs_equiv_one_fin_of_free_range](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma equiv_one_fin_of_free_range
  {R : Type u} [CommRing R]
  {ι : Type v} [Fintype ι]
-- given
  (E : Matrix ι ι R)
  (hE : E * E = E)
  [Module.Free R (LinearMap.range E.mulVecLin)]
  [Module.Finite R (LinearMap.range E.mulVecLin)] :
-- imply
  ∃ n : ℕ, qsMatrixEquiv E (1 : Matrix (Fin n) (Fin n) R) := by
-- proof
  apply qs_equiv_one_fin_of_free_range E hE


/--
[qs_residue_equiv_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma residue_equiv_one
  [CommRing R] [IsLocalRing R] [Fintype ι]
-- given
  (E : Matrix ι ι (Polynomial R))
  (hE : E * E = E) :
-- imply
  ∃ n : ℕ, qsMatrixEquiv (E.map (Polynomial.mapRingHom (IsLocalRing.residue R))) (1 : Matrix (Fin n) (Fin n) (Polynomial (IsLocalRing.ResidueField R))) := by
-- proof
  apply qs_residue_equiv_one R E hE


/--
[qs_fin_eq_of_one_equiv_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma fin_eq_of_one_equiv_one
  [Field K]
  {n m : ℕ}
-- given
  (h : qsMatrixEquiv (1 : Matrix (Fin n) (Fin n) K)
      (1 : Matrix (Fin m) (Fin m) K)) :
-- imply
  n = m := by
-- proof
  apply qs_fin_eq_of_one_equiv_one h


/--
[qs_residue_equiv_one_same_rank](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma residue_equiv_one_same_rank
  [CommRing R] [IsLocalRing R] [Fintype ι]
-- given
  (E : Matrix ι ι (Polynomial R))
  {m : ℕ}
  (hE : E * E = E)
  (hQ : qsMatrixEquiv
      (E.map (algebraMap (Polynomial R)
        (Localization (qsMonicSubmonoid R))))
      (1 : Matrix (Fin m) (Fin m)
        (Localization (qsMonicSubmonoid R)))) :
-- imply
  qsMatrixEquiv (E.map (Polynomial.mapRingHom (IsLocalRing.residue R))) (1 : Matrix (Fin m) (Fin m) (Polynomial (IsLocalRing.ResidueField R))) := by
-- proof
  apply qs_residue_equiv_one_same_rank R E hE hQ


/--
[qs_horrocks_adjusted_factors](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma horrocks_adjusted_factors
  [CommRing R] [IsLocalRing R] [Fintype ι]
-- given
  (E : Matrix ι ι (Polynomial R))
  {m : ℕ}
  (hE : E * E = E)
  (hQ : qsMatrixEquiv
      (E.map (algebraMap (Polynomial R)
        (Localization (qsMonicSubmonoid R))))
      (1 : Matrix (Fin m) (Fin m)
        (Localization (qsMonicSubmonoid R)))) :
-- imply
  ∃ A : Matrix ι (Fin m) (Localization (qsMonicSubmonoid R)), ∃ B : Matrix (Fin m) ι (Localization (qsMonicSubmonoid R)), A * B = E.map (algebraMap (Polynomial R) (Localization (qsMonicSubmonoid R))) ∧ B * A = 1 ∧ qsResiduePolynomialMatrix R A ∧ qsResiduePolynomialMatrix R B := by
-- proof
  apply qs_horrocks_adjusted_factors R E hE hQ


/--
[qs_horrocks_local](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma horrocks_local
  [CommRing R] [IsLocalRing R] [Fintype ι]
-- given
  (E : Matrix ι ι (Polynomial R))
  {m : ℕ}
  (hE : E * E = E)
  (hQ : qsMatrixEquiv
      (E.map (algebraMap (Polynomial R)
        (Localization (qsMonicSubmonoid R))))
      (1 : Matrix (Fin m) (Fin m)
        (Localization (qsMonicSubmonoid R)))) :
-- imply
  qsMatrixEquiv E (1 : Matrix (Fin m) (Fin m) (Polynomial R)) := by
-- proof
  apply qs_horrocks_local R E hE hQ


/--
[qs_free_range_of_equiv_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma free_range_of_equiv_one
  [CommRing R] [Fintype ι] [Fintype κ]
  [DecidableEq κ]
  {E : Matrix ι ι R}
-- given
  (h : qsMatrixEquiv E (1 : Matrix κ κ R)) :
-- imply
  Module.Free R (LinearMap.range E.mulVecLin) := by
-- proof
  apply qs_free_range_of_equiv_one h


/--
[qs_exists_idempotent_range_equiv](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma exists_idempotent_range_equiv
  {R : Type u} [CommRing R]
  {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M] :
-- imply
  ∃ (n : ℕ) (E : Matrix (Fin n) (Fin n) R), E * E = E ∧ Nonempty (LinearEquiv (RingHom.id R) M (LinearMap.range E.mulVecLin)) := by
-- proof
  apply qs_exists_idempotent_range_equiv


/--
[qs_free_of_matrix_equiv_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma free_of_matrix_equiv_one
  [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι] [Fintype κ]
  [DecidableEq κ]
  {E : Matrix ι ι R}
-- given
  (h : qsMatrixEquiv E (1 : Matrix κ κ R))
  (e : LinearEquiv (RingHom.id R) M (LinearMap.range E.mulVecLin)) :
-- imply
  Module.Free R M := by
-- proof
  apply qs_free_of_matrix_equiv_one e h


/--
[qs_zero_variables](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma zero_variables
  [Field k] [AddCommGroup M] [Module (MvPolynomial (Fin 0) k) M] :
-- imply
  Module.Free (MvPolynomial (Fin 0) k) M := by
-- proof
  apply qs_zero_variables


/--
[qs_idempotent_free](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma idempotent_free
  [Field k] [Fintype ι]
-- given
  (n : ℕ)
  (E : Matrix ι ι (MvPolynomial (Fin n) k))
  (hE : E * E = E) :
-- imply
  ∃ m : ℕ, qsMatrixEquiv E (1 : Matrix (Fin m) (Fin m) (MvPolynomial (Fin n) k)) := by
-- proof
  apply qs_idempotent_free n k E hE


/--
[quillen_suslin](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Module/QuillenSuslin.lean)
-/
@[path]
private lemma free_of_fg_projective
  [Field k] [AddCommGroup M]
  {n : ℕ} [Module (MvPolynomial (Fin n) k) M] [Module.Finite (MvPolynomial (Fin n) k) M] [Module.Projective (MvPolynomial (Fin n) k) M] :
-- imply
  Module.Free (MvPolynomial (Fin n) k) M := by
-- proof
  apply quillen_suslin


-- created on 2026-10-09
