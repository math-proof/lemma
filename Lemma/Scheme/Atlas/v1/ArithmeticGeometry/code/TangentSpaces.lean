import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.ArithmeticGeometry.code.TangentSpaces.Part4
open Matrix Module Submodule LinearMap FiniteDimensional MvPolynomial IntermediateField Cardinal in IsLocalRing TangentSpaces SingularLocus
open IntermediateField Cardinal
open MvPolynomial Matrix
open IsLocalRing Module


/--
[totalDerivativeAt_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/TangentSpaces.lean)
-/
@[path]
lemma totalDerivativeAt_add
  [Field k]
  {n : ℕ}
  {f g : MvPolynomial (Fin n) k}
  {P v : Fin n → k} :
-- imply
  totalDerivativeAt (f + g) P v = totalDerivativeAt f P v + totalDerivativeAt g P v := by
-- proof
  simp only [totalDerivativeAt, map_add, add_mul, Finset.sum_add_distrib]

/--
[totalDerivativeAt_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/TangentSpaces.lean)
-/
@[path]
lemma totalDerivativeAt_zero
  [Field k]
  {n : ℕ}
  {P v : Fin n → k} :
-- imply
  totalDerivativeAt 0 P v = 0 := by
-- proof
  simp [totalDerivativeAt, map_zero]

/--
[totalDerivativeAt_mul_of_eval_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/TangentSpaces.lean)
-/
@[path]
lemma totalDerivativeAt_mul_of_eval_eq_zero
  [Field k]
  {n : ℕ}
  {r g : MvPolynomial (Fin n) k}
  {P v : Fin n → k}
-- given
  (hg : MvPolynomial.eval P g = 0) :
-- imply
  totalDerivativeAt (r * g) P v = MvPolynomial.eval P r * totalDerivativeAt g P v := by
-- proof
  simp only [totalDerivativeAt, pderiv_mul, map_add, MvPolynomial.eval_mul, hg,
    mul_zero, zero_add]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _; ring

/--
[totalDerivativeAt_smul_of_eval_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/TangentSpaces.lean)
-/
@[path]
lemma totalDerivativeAt_smul_of_eval_eq_zero
  [Field k]
  {n : ℕ}
  {r g : MvPolynomial (Fin n) k}
  {P v : Fin n → k}
-- given
  (hg : MvPolynomial.eval P g = 0) :
-- imply
  totalDerivativeAt (r • g) P v = MvPolynomial.eval P r * totalDerivativeAt g P v := by
-- proof
  rw [smul_eq_mul]
  exact totalDerivativeAt_mul_of_eval_eq_zero r g P v hg

/--
[tangentSpaceIdeal_eq_iInf_generators](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/TangentSpaces.lean)
-/
@[path]
lemma tangentSpaceIdeal_eq_iInf_generators
  [Field k]
  {n : ℕ}
  {m : ℕ}
  {f : Fin m → MvPolynomial (Fin n) k}
  {P : Fin n → k}
-- given
  (hP : ∀ g ∈ Ideal.span (Set.range f), MvPolynomial.eval P g = 0) :
-- imply
  tangentSpaceIdeal (Ideal.span (Set.range f)) P = ⨅ i : Fin m, tangentSpacePoly (f i) P := by
-- proof
  ext v
  simp only [tangentSpaceIdeal, Submodule.mem_iInf, tangentSpacePoly, LinearMap.mem_ker,
    totalDerivativeAtLin, LinearMap.coe_mk, AddHom.coe_mk]
  constructor
  · intro h i
    exact h (f i) (Ideal.subset_span (Set.mem_range_self i))
  · intro h g hg
    refine Submodule.span_induction
      (p := fun g _ => totalDerivativeAt g P v = 0) ?_ ?_ ?_ ?_ hg
    · rintro g ⟨i, rfl⟩
      exact h i
    · exact totalDerivativeAt_zero P v
    · intro g₁ g₂ _ _ h₁ h₂
      rw [totalDerivativeAt_add, h₁, h₂, add_zero]
    · intro r g hg_mem hg_val
      rw [totalDerivativeAt_smul_of_eval_eq_zero r g P v (hP g hg_mem), hg_val, mul_zero]

/--
[tangentSpace_eq_ker_jacobian](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/TangentSpaces.lean)
-/
@[path]
lemma tangentSpace_eq_ker_jacobian
  [Field k]
  {n : ℕ}
  {m : ℕ}
  {f : Fin m → MvPolynomial (Fin n) k}
  {P : Fin n → k} :
-- imply
  (⨅ i : Fin m, tangentSpacePoly (f i) P) = LinearMap.ker (Matrix.of (fun i j => MvPolynomial.eval P (MvPolynomial.pderiv j (f i))) : Matrix (Fin m) (Fin n) k).mulVecLin := by
-- proof
  ext v
  simp only [Submodule.mem_iInf, tangentSpacePoly, LinearMap.mem_ker,
    totalDerivativeAtLin, LinearMap.coe_mk, AddHom.coe_mk, mulVecLin_apply]
  constructor
  · intro h
    ext i
    simp only [mulVec, dotProduct, Pi.zero_apply]
    convert h i using 1
  · intro h i
    have := congr_fun h i
    simp only [mulVec, dotProduct, Pi.zero_apply] at this
    simp only [totalDerivativeAt]
    convert this using 1

/--
[tangentSpace_eq_ker_jointLinearizationMap](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/TangentSpaces.lean)
-/
@[path]
lemma tangentSpace_eq_ker_jointLinearizationMap
  [Field k]
  {n : ℕ}
  {m : ℕ}
  {f : Fin m → MvPolynomial (Fin n) k}
  {P : Fin n → k} :
-- imply
  (⨅ i : Fin m, tangentSpacePoly (f i) P) = LinearMap.ker (jointLinearizationMap f P) := by
-- proof
  ext v
  simp [Submodule.mem_iInf, tangentSpacePoly, LinearMap.mem_ker, jointLinearizationMap,
    totalDerivativeAtLin, LinearMap.coe_mk, AddHom.coe_mk, funext_iff]

/--
[cotangentSpace_dualAnnihilator_eq_range_dualMap](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/TangentSpaces.lean)
-/
@[path]
lemma cotangentSpace_dualAnnihilator_eq_range_dualMap
  [Field k]
  {n : ℕ}
  {m : ℕ}
  {f : Fin m → MvPolynomial (Fin n) k}
  {P : Fin n → k} :
-- imply
  (⨅ i : Fin m, tangentSpacePoly (f i) P).dualAnnihilator = LinearMap.range (jointLinearizationMap f P).dualMap := by
-- proof
  rw [tangentSpace_eq_ker_jointLinearizationMap]
  exact (LinearMap.range_dualMap_eq_dualAnnihilator_ker (jointLinearizationMap f P)).symm
namespace TangentSpaces
variable {k : Type*} [Field k]

namespace TangentSpaces

/--
[tangent_dim_eq_sub_jacobian_rank](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/TangentSpaces.lean)
-/
@[path]
lemma tangent_dim_eq_sub_jacobian_rank
  [Field k]
  {m n : ℕ}
  {M : Matrix (Fin m) (Fin n) k} :
-- imply
  finrank k (tangentSpace M) = n - M.rank := by
-- proof
  unfold tangentSpace Matrix.rank
  have h := finrank_range_add_finrank_ker M.mulVecLin
  simp only [finrank_fintype_fun_eq_card, Fintype.card_fin] at h
  omega

end TangentSpaces

namespace TangentSpaces

/--
[jacobian_rank_add_tangent_dim](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/TangentSpaces.lean)
-/
@[path]
lemma jacobian_rank_add_tangent_dim
  [Field k]
  {m n : ℕ}
  {M : Matrix (Fin m) (Fin n) k} :
-- imply
  M.rank + finrank k (tangentSpace M) = n := by
-- proof
  unfold tangentSpace Matrix.rank
  have h := finrank_range_add_finrank_ker M.mulVecLin
  simp only [finrank_fintype_fun_eq_card, Fintype.card_fin] at h
  omega

end TangentSpaces

namespace TangentSpaces

/--
[jacobian_rank_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/TangentSpaces.lean)
-/
@[path]
lemma jacobian_rank_le
  [Field k]
  {m n : ℕ}
  {M : Matrix (Fin m) (Fin n) k} :
-- imply
  M.rank ≤ n := by
-- proof
  have h := jacobian_rank_add_tangent_dim M
  omega

end TangentSpaces

namespace TangentSpaces

/--
[tangentSpace_jacobian_eq_tangentSpaceIdeal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/TangentSpaces.lean)
-/
@[path]
lemma tangentSpace_jacobian_eq_tangentSpaceIdeal
  [Field k]
  {n m : ℕ}
  {f : Fin m → MvPolynomial (Fin n) k}
  {P : Fin n → k}
-- given
  (hP : ∀ g ∈ Ideal.span (Set.range f), MvPolynomial.eval P g = 0) :
-- imply
  tangentSpace (jacobianMatrix n m f P) = tangentSpaceIdeal (Ideal.span (Set.range f)) P := by
-- proof
  rw [tangentSpaceIdeal_eq_iInf_generators f P hP]
  exact (tangentSpace_eq_ker_jacobian f P).symm

end TangentSpaces

namespace TangentSpaces

/--
[rank_le_one_of_single_row](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/TangentSpaces.lean)
-/
@[path]
lemma rank_le_one_of_single_row
  [Field k]
  {n : ℕ}
  {M : Matrix (Fin 1) (Fin n) k} :
-- imply
  M.rank ≤ 1 := by
-- proof
  unfold Matrix.rank
  calc finrank k (LinearMap.range M.mulVecLin)
    ≤ finrank k (Fin 1 → k) := Submodule.finrank_le _
    _ = 1 := by simp [finrank_fintype_fun_eq_card]
end TangentSpaces
open IntermediateField Cardinal

end TangentSpaces

/--
[function_field_generated_by_n_plus_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/TangentSpaces.lean)
-/
@[path]
lemma function_field_generated_by_n_plus_one
  {k : Type*}
  {F : Type*}
  [Field k]
  [IsAlgClosed k]
  [Field F]
  [Algebra k F]
  {n : ℕ}
-- given
  (hfg : (⊤ : IntermediateField k F).FG)
  (htrdeg : Algebra.trdeg k F = n) :
-- imply
  ∃ (α : Fin (n + 1) → F), AlgebraicIndependent k (fun i : Fin n => α (Fin.castSucc i)) ∧ IntermediateField.adjoin k (Set.range α) = ⊤ := by
-- proof
  haveI : Algebra.EssFiniteType k F := IntermediateField.fg_top_iff.mp hfg
  obtain ⟨t, α, ht_indep, _, ht_gen⟩ := function_field_generators k F n htrdeg
  refine ⟨Fin.snoc t α, ?_, ?_⟩
  · convert ht_indep using 1
    simp only [Fin.snoc_castSucc]
  · rw [Fin.range_snoc]
    exact ht_gen

/--
[functionField_fg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/TangentSpaces.lean)
-/
@[path]
lemma functionField_fg
  {k : Type*}
  [Field k]
  {N : ℕ}
  {V : Set (AffineSpace_k k N)}
-- given
  (hV : IsAffineVariety k N V) :
-- imply
  (⊤ : IntermediateField (AlgebraicClosure k) (functionField k N V hV)).FG := by
-- proof
  rw [IntermediateField.fg_top_iff]
  letI : IsDomain (MvPolynomial (Fin N) (AlgebraicClosure k) ⧸ idealOfAlgebraicSet V) :=
    coordinateRingBar_isDomain' k N V hV
  show Algebra.EssFiniteType (AlgebraicClosure k)
    (FractionRing (MvPolynomial (Fin N) (AlgebraicClosure k) ⧸ idealOfAlgebraicSet V))
  haveI : Algebra.EssFiniteType (MvPolynomial (Fin N) (AlgebraicClosure k) ⧸ idealOfAlgebraicSet V)
    (FractionRing (MvPolynomial (Fin N) (AlgebraicClosure k) ⧸ idealOfAlgebraicSet V)) :=
    Algebra.EssFiniteType.of_isLocalization _ (nonZeroDivisors _)
  exact Algebra.EssFiniteType.comp (AlgebraicClosure k)
    (MvPolynomial (Fin N) (AlgebraicClosure k) ⧸ idealOfAlgebraicSet V) _

/--
[irreducible_poly_vanishing_on_generators](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/TangentSpaces.lean)
-/
@[path]
lemma irreducible_poly_vanishing_on_generators
  {k : Type*}
  [Field k]
  [IsAlgClosed k]
  {n : ℕ}
  {F : Type*}
  [Field F]
  [Algebra (AlgebraicClosure k) F]
  {α : Fin (n + 1) → F}
-- given
  (h_indep : AlgebraicIndependent (AlgebraicClosure k) (fun i : Fin n => α (Fin.castSucc i)))
  (h_gen : IntermediateField.adjoin (AlgebraicClosure k) (Set.range α) = ⊤)
  (h_not_indep : ¬ AlgebraicIndependent (AlgebraicClosure k) α) :
-- imply
  ∃ (f : MvPolynomial (Fin (n + 1)) (AlgebraicClosure k)), Irreducible f ∧ MvPolynomial.aeval α f = 0 := by
-- proof
  rw [algebraicIndependent_iff_injective_aeval] at h_not_indep
  have hker_ne_bot : RingHom.ker (MvPolynomial.aeval α :
    MvPolynomial (Fin (n + 1)) (AlgebraicClosure k) →ₐ[AlgebraicClosure k] F) ≠ ⊥ := by
    intro h
    exact h_not_indep ((RingHom.injective_iff_ker_eq_bot _).mpr h)
  have hker_prime : (RingHom.ker (MvPolynomial.aeval α :
    MvPolynomial (Fin (n + 1)) (AlgebraicClosure k) →ₐ[AlgebraicClosure k] F)).IsPrime :=
    RingHom.ker_isPrime _
  obtain ⟨f, hf_mem, hf_prime⟩ := hker_prime.exists_mem_prime_of_ne_bot hker_ne_bot
  exact ⟨f, hf_prime.irreducible, by rwa [RingHom.mem_ker] at hf_mem⟩

/--
[nullstellensatz_irreducible](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/TangentSpaces.lean)
-/
@[path]
lemma nullstellensatz_irreducible
  {k : Type*}
  [Field k]
  [IsAlgClosed k]
  {N : ℕ}
  {f : MvPolynomial (Fin N) (AlgebraicClosure k)}
-- given
  (hf_irred : Irreducible f) :
-- imply
  idealOfAlgebraicSet (AlgebraicSet k N ({f} : Set (MvPolynomial (Fin N) (AlgebraicClosure k)))) = Ideal.span {f} := by
-- proof
  have hset : AlgebraicSet k N {f} = AlgebraicSet k N (Ideal.span {f} : Set _) := by
    ext P
    simp only [AlgebraicSet, Set.mem_setOf_eq]
    constructor
    · intro hP g hg
      induction hg using Submodule.span_induction with
      | mem x hx =>
        simp only [Set.mem_singleton_iff] at hx
        rw [hx]; exact hP f (Set.mem_singleton f)
      | zero => simp
      | add x y _ _ hx hy => simp [map_add, hx, hy]
      | smul a x _ hx => simp [map_mul, hx]
    · intro hP g hg
      exact hP g (Ideal.subset_span hg)
  rw [hset, hilbert_nullstellensatz k]
  have hprime : (Ideal.span {f}).IsPrime := by
    rwa [Ideal.span_singleton_prime (Irreducible.ne_zero hf_irred)]
  exact hprime.radical

/--
[hypersurface_isAffineVariety](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/TangentSpaces.lean)
-/
@[path]
lemma hypersurface_isAffineVariety
  {k : Type*}
  [Field k]
  {N : ℕ}
  {f : MvPolynomial (Fin N) (AlgebraicClosure k)}
-- given
  (hf : Irreducible f) :
-- imply
  IsAffineVariety k N (AlgebraicSet k N {f}) := by
-- proof
  constructor
  ·
    exact algebraicSet_isAlgebraicSubset k {f}
  ·
    rw [isIrreducibleAlgebraicSet_iff_isPrime k (algebraicSet_isAlgebraicSubset k {f})]
    have hset : AlgebraicSet k N {f} = AlgebraicSet k N (Ideal.span {f} : Set _) := by
      ext P
      simp only [AlgebraicSet, Set.mem_setOf_eq]
      constructor
      · intro hP g hg
        induction hg using Submodule.span_induction with
        | mem x hx =>
          simp only [Set.mem_singleton_iff] at hx
          rw [hx]; exact hP f (Set.mem_singleton f)
        | zero => simp
        | add x y _ _ hx hy => simp [map_add, hx, hy]
        | smul a x _ hx => simp [map_mul, hx]
      · intro hP g hg
        exact hP g (Ideal.subset_span hg)
    rw [hset, hilbert_nullstellensatz k]
    have hprime : (Ideal.span {f}).IsPrime := by
      rwa [Ideal.span_singleton_prime (Irreducible.ne_zero hf)]
    rwa [hprime.radical]

/--
[isHypersurface_of_irreducible](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/TangentSpaces.lean)
-/
@[path]
lemma isHypersurface_of_irreducible
  {k : Type*}
  [Field k]
  [IsAlgClosed k]
  {N : ℕ}
  {f : MvPolynomial (Fin N) (AlgebraicClosure k)}
-- given
  (hf : Irreducible f) :
-- imply
  IsHypersurface k N (AlgebraicSet k N {f}) := by
-- proof
  refine ⟨hypersurface_isAffineVariety k N f hf, ?_, ?_⟩
  ·
    rw [nullstellensatz_irreducible k N f hf]
    exact ⟨⟨f, rfl⟩⟩
  ·
    rw [nullstellensatz_irreducible k N f hf]
    intro h
    have : f ∈ (⊥ : Ideal (MvPolynomial (Fin N) (AlgebraicClosure k))) := by
      rw [← h]; exact Ideal.subset_span (Set.mem_singleton f)
    simp at this
    exact hf.ne_zero this

/--
[IsHypersurface.exists_irreducible](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/TangentSpaces.lean)
-/
@[path]
lemma IsHypersurface.exists_irreducible
  [Field k]
  {N : ℕ}
  {W : Set (AffineSpace_k k N)}
-- given
  (hW : IsHypersurface k N W) :
-- imply
  ∃ f : MvPolynomial (Fin N) (AlgebraicClosure k), Irreducible f ∧ W = AlgebraicSet k N {f} := by
-- proof
  obtain ⟨hVar, hPrinc, hNe⟩ := hW
  obtain ⟨g, hg⟩ := hPrinc.principal
  have hg_ne : g ≠ 0 := by
    intro heq; apply hNe; rw [hg, heq]; simp [Submodule.span_singleton_eq_bot]
  have hprime := (isIrreducibleAlgebraicSet_iff_isPrime k hVar.1).mp hVar.2
  rw [hg] at hprime
  have hg_prime : Prime g := by
    have : (Ideal.span {g}).IsPrime := by convert hprime
    rwa [Ideal.span_singleton_prime hg_ne] at this
  have hg_irred : Irreducible g := hg_prime.irreducible
  refine ⟨g, hg_irred, ?_⟩
  have h_VIW : W = AlgebraicSet k N (idealOfAlgebraicSet W : Set _) :=
    (algebraicSet_idealOfAlgebraicSet_of_isAlgebraicSubset k hVar.1).symm
  rw [hg] at h_VIW
  convert h_VIW using 1
  ext P
  simp only [AlgebraicSet, Set.mem_setOf_eq, SetLike.mem_coe]
  constructor
  · intro hP f hf
    have hfg : f ∈ (MvPolynomial (Fin N) (AlgebraicClosure k) ∙ g) := hf
    simp only [Submodule.mem_span_singleton] at hfg
    obtain ⟨c, rfl⟩ := hfg
    simp [MvPolynomial.eval_mul, hP g (Set.mem_singleton g)]
  · intro hP f hf
    have hfg : f = g := Set.mem_singleton_iff.mp hf
    rw [hfg]
    exact hP g (Submodule.mem_span_singleton_self g)

namespace SingularLocus

/--
[rank_lt_iff_all_minors_det_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/TangentSpaces.lean)
-/
@[path]
lemma rank_lt_iff_all_minors_det_eq_zero
  {k : Type*}
  [Field k]
  [Field k']
  {m n r : ℕ}
  {M : Matrix (Fin m) (Fin n) k'} :
-- imply
  M.rank < r ↔ ∀ (ri : Fin r → Fin m) (ci : Fin r → Fin n), (M.submatrix ri ci).det = 0 := by
-- proof
  constructor
  ·
    intro hrank ri ci
    by_contra hne
    have hdet : IsUnit (M.submatrix ri ci).det := isUnit_iff_ne_zero.mpr hne
    have hU : IsUnit (M.submatrix ri ci) := (Matrix.isUnit_iff_isUnit_det _).mpr hdet
    have hrank_sub : (M.submatrix ri ci).rank = r := by
      apply le_antisymm
      · calc (M.submatrix ri ci).rank ≤ Fintype.card (Fin r) :=
        (M.submatrix ri ci).rank_le_card_width
        _ = r := Fintype.card_fin r
      · calc r = Fintype.card (Fin r) := (Fintype.card_fin r).symm
        _ = (1 : Matrix (Fin r) (Fin r) k').rank := by simp [Matrix.rank_one]
        _ = ((M.submatrix ri ci)⁻¹ * (M.submatrix ri ci)).rank := by
          rw [Matrix.nonsing_inv_mul _ hdet]
        _ ≤ (M.submatrix ri ci).rank := Matrix.rank_mul_le_right _ _
    have hsub : (M.submatrix ri ci).rank ≤ M.rank := by
      let P : Matrix (Fin r) (Fin m) k' := Matrix.of fun i j => if j = ri i then (1:k') else 0
      let Q : Matrix (Fin n) (Fin r) k' := Matrix.of fun i j => if i = ci j then (1:k') else 0
      have hPMQ : M.submatrix ri ci = P * M * Q := by
        ext i j
        simp only [P, Q, Matrix.submatrix_apply, Matrix.mul_apply, Matrix.of_apply]
        have h1 : ∀ x, (∑ x_1, (if x_1 = ri i then (1:k') else 0) * M x_1 x) =
          M (ri i) x := by
          intro x; rw [Finset.sum_eq_single (ri i)]; simp; intro b _ hb; simp [hb]
          exact fun h => absurd (Finset.mem_univ _) h
        simp_rw [h1]; rw [Finset.sum_eq_single (ci j)]; simp; intro b _ hb; simp [hb]
        exact fun h => absurd (Finset.mem_univ _) h
      rw [hPMQ, Matrix.mul_assoc]
      exact (Matrix.rank_mul_le_right _ _).trans (Matrix.rank_mul_le_left _ _)
    omega
  ·
    intro hMinors
    by_contra h
    simp only [not_lt] at h
    obtain ⟨κ, a, ha_inj, ha_span, ha_li⟩ := exists_linearIndependent' k' M.col
    haveI : Fintype κ := Fintype.ofInjective a ha_inj
    have hcard : Fintype.card κ = M.rank := by
      have h1 := finrank_span_eq_card ha_li
      rw [ha_span] at h1; rw [← Matrix.rank_eq_finrank_span_cols] at h1; omega
    classical
    let ci := a ∘ (Fintype.equivFin κ).symm ∘ Fin.castLE (hcard ▸ h)
    have hci : LinearIndependent k' (M.col ∘ ci) :=
      ha_li.comp _ ((Fintype.equivFin κ).symm.injective.comp (Fin.castLE_injective _))
    let N := M.submatrix _root_.id ci
    have hN_rank : N.rank = r := by
      rw [Matrix.rank_eq_finrank_span_cols]
      have : N.col = M.col ∘ ci := by
        ext j i; simp [N, Matrix.submatrix_apply, Matrix.col_apply]
      rw [this, finrank_span_eq_card hci, Fintype.card_fin]
    have hNt : N.transpose.rank = r := by rw [Matrix.rank_transpose]; exact hN_rank
    obtain ⟨κ₂, a₂, ha2_inj, ha2_span, ha2_li⟩ := exists_linearIndependent' k' N.transpose.col
    haveI : Fintype κ₂ := Fintype.ofInjective a₂ ha2_inj
    have hcard₂ : Fintype.card κ₂ = r := by
      have h2 := finrank_span_eq_card ha2_li
      rw [ha2_span, ← Matrix.rank_eq_finrank_span_cols, hNt] at h2; omega
    let ri := a₂ ∘ (Fintype.equivFin κ₂).symm ∘ Fin.castLE hcard₂.ge
    have hri : LinearIndependent k' (N.transpose.col ∘ ri) :=
      ha2_li.comp _ ((Fintype.equivFin κ₂).symm.injective.comp (Fin.castLE_injective _))
    have hrows : LinearIndependent k' (M.submatrix ri ci).row := by
      have key : (M.submatrix ri ci).row = N.transpose.col ∘ ri := by
        ext i j
        simp [Matrix.row_apply, Matrix.submatrix_apply, Matrix.col_apply,
          Matrix.transpose_apply, N]
      rw [key]; exact hri
    have hU := Matrix.linearIndependent_rows_iff_isUnit.mp hrows
    exact ((Matrix.isUnit_iff_isUnit_det _).mp hU).ne_zero (hMinors ri ci)

end SingularLocus

namespace SingularLocus

/--
[eval_minor_det_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/TangentSpaces.lean)
-/
@[path]
lemma eval_minor_det_eq
  {k : Type*}
  [Field k]
  {n m r : ℕ}
  {f : Fin m → MvPolynomial (Fin n) (AlgebraicClosure k)}
  {P : Fin n → AlgebraicClosure k}
  {ri : Fin r → Fin m}
  {ci : Fin r → Fin n} :
-- imply
  MvPolynomial.eval P (((jacobianPolyMatrix k n m f).submatrix ri ci).det) = ((TangentSpaces.jacobianMatrix n m f P).submatrix ri ci).det := by
-- proof
  rw [RingHom.map_det]
  congr 1

end SingularLocus

namespace SingularLocus

/--
[mem_singularLocusAlgebraic_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/TangentSpaces.lean)
-/
@[path]
lemma mem_singularLocusAlgebraic_iff
  {k : Type*}
  [Field k]
  {n m r : ℕ}
  {f : Fin m → MvPolynomial (Fin n) (AlgebraicClosure k)}
  {P : AffineSpace_k k n} :
-- imply
  P ∈ singularLocusAlgebraic k n m r f ↔ (∀ i, MvPolynomial.eval P (f i) = 0) ∧ (∀ (ri : Fin r → Fin m) (ci : Fin r → Fin n), ((TangentSpaces.jacobianMatrix n m f P).submatrix ri ci).det = 0) := by
-- proof
  constructor
  · intro hP
    constructor
    · intro i
      exact hP (f i) (Set.mem_union_left _ (Set.mem_range_self i))
    · intro ri ci
      have hd := hP _ (Set.mem_union_right _ ⟨ri, ci, rfl⟩)
      rwa [eval_minor_det_eq] at hd
  · intro ⟨hV, hminors⟩ g hg
    obtain ⟨i, rfl⟩ | ⟨ri, ci, rfl⟩ := hg
    · exact hV i
    · rw [eval_minor_det_eq]
      exact hminors ri ci

end SingularLocus

namespace SingularLocus

/--
[singularLocus_eq_algebraicSet](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/TangentSpaces.lean)
-/
@[path]
lemma singularLocus_eq_algebraicSet
  {k : Type*}
  [Field k]
  {n m r : ℕ}
  {f : Fin m → MvPolynomial (Fin n) (AlgebraicClosure k)} :
-- imply
  singularLocusIntrinsic k n m r f = singularLocusAlgebraic k n m r f := by
-- proof
  ext P
  simp only [singularLocusIntrinsic, Set.mem_setOf_eq]
  rw [mem_singularLocusAlgebraic_iff]
  constructor
  · intro ⟨hPV, hrank⟩
    refine ⟨fun i => hPV (f i) (Set.mem_range_self i), ?_⟩
    exact (rank_lt_iff_all_minors_det_eq_zero _).mp hrank
  · intro ⟨hPolys, hMinors⟩
    refine ⟨fun g hg => ?_, (rank_lt_iff_all_minors_det_eq_zero _).mpr hMinors⟩
    obtain ⟨i, rfl⟩ := hg
    exact hPolys i

end SingularLocus

namespace SingularLocus

/--
[singular_locus_is_closed_subset](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/TangentSpaces.lean)
-/
@[path]
lemma singular_locus_is_closed_subset
  {k : Type*}
  [Field k]
  {k : Type*}
  [Field k]
  {n m r : ℕ}
  {f : Fin m → MvPolynomial (Fin n) (AlgebraicClosure k)} :
-- imply
  IsAlgebraicSubset k n (singularLocusIntrinsic k n m r f) ∧ singularLocusIntrinsic k n m r f ⊆ AlgebraicSet k n (Set.range f) := by
-- proof
  constructor
  ·
    rw [singularLocus_eq_algebraicSet]
    exact algebraicSet_isAlgebraicSubset k _
  ·
    intro P hP
    exact hP.1
end SingularLocus
open IsLocalRing Module
section Corollary_17_14


/--
[cotangent_finrank_eq_derivation_finrank](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/TangentSpaces.lean)
-/
@[path]
lemma cotangent_finrank_eq_derivation_finrank
  [CommRing R]
  [IsLocalRing R]
  [Field k]
  [Algebra k R]
  [Algebra R k]
  [IsScalarTower k R k]
  {e : Dual k (CotangentSpace R) ≃ₗ[k] Derivation k R k} :
-- imply
  finrank k (CotangentSpace R) = finrank k (Derivation k R k) := by
-- proof
  have h1 : finrank k (Dual k (CotangentSpace R)) = finrank k (CotangentSpace R) :=
    Subspace.dual_finrank_eq
  have h2 : finrank k (Dual k (CotangentSpace R)) = finrank k (Derivation k R k) :=
    LinearEquiv.finrank_eq e
  linarith
end Corollary_17_14

/--
[coordinateRingBar_isDomain'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/TangentSpaces.lean)
-/
@[path]
private lemma coordinateRingBar_isDomain'_eq
  {k : Type*}
  [Field k]
  {N : ℕ}
  {V : Set (AffineSpace_k k N)}
-- given
  (hV : IsAffineVariety k N V) :
-- imply
  IsDomain (AffineCoordinateRingBar V) := by
-- proof
  apply coordinateRingBar_isDomain' k N V hV


-- created on 2026-10-23
