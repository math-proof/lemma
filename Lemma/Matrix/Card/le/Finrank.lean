import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraNotes.code.GaloisTheory
open GaloisTheory


namespace GaloisTheory

/--
[card_aut_le_finrank](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/GaloisTheory.lean)
-/
@[path]
lemma card_aut_le_finrank
  [Field F]
  [Field E]
  [Algebra F E]
  {F E : Type*}
  [Field F]
  [Field E]
  [Algebra F E]
  [FiniteDimensional F E]
  [Algebra.IsSeparable F E] :
-- imply
  Nat.card (E ≃ₐ[F] E) ≤ Module.finrank F E := by
-- proof
  rwa [Nat.card_eq_fintype_card]

end GaloisTheory

namespace GaloisTheory

/--
[isGalois_iff_card_aut_eq_finrank](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/GaloisTheory.lean)
-/
@[path]
lemma isGalois_iff_card_aut_eq_finrank
  [Field F]
  [Field E]
  [Algebra F E]
  {F E : Type*}
  [Field F]
  [Field E]
  [Algebra F E]
  [FiniteDimensional F E] :
-- imply
  IsGalois F E ↔ Nat.card (E ≃ₐ[F] E) = Module.finrank F E :=
-- proof
  ⟨fun _ => IsGalois.card_aut_eq_finrank F E,
    fun h => IsGalois.of_card_aut_eq_finrank F E h⟩

end GaloisTheory

namespace GaloisTheory

/--
[galois_group_size](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/GaloisTheory.lean)
-/
@[path]
lemma galois_group_size
  [Field F]
  [Field E]
  [Algebra F E]
  {F E : Type*}
  [Field F]
  [Field E]
  [Algebra F E]
  [FiniteDimensional F E]
  [Algebra.IsSeparable F E] :
-- imply
  (Nat.card (E ≃ₐ[F] E) ≤ Module.finrank F E) ∧ (IsGalois F E ↔ Nat.card (E ≃ₐ[F] E) = Module.finrank F E) :=
-- proof
  ⟨card_aut_le_finrank F E, isGalois_iff_card_aut_eq_finrank F E⟩

end GaloisTheory

namespace GaloisTheory

/--
[symmetric_polynomial_in_esymm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/GaloisTheory.lean)
-/
@[path]
lemma symmetric_polynomial_in_esymm
  [Field F]
  [Field E]
  [Algebra F E]
  [Field F]
  {P : Polynomial F}
  {n : ℕ}
  {f : MvPolynomial (Fin n) F}
  {α : Fin n → F}
-- given
  (hP : P.Monic)
  (hsplit : P.Splits)
  (hn : P.natDegree = n)
  (hf : f.IsSymmetric)
  (hα : P = ∏ i : Fin n, (Polynomial.X - Polynomial.C (α i))) :
-- imply
  ∃ q : MvPolynomial (Fin n) F, MvPolynomial.eval α f = MvPolynomial.eval (fun i : Fin n => (-1 : F) ^ (i.val + 1) * P.coeff (n - (i.val + 1))) q := by
-- proof
  have hcard : Fintype.card (Fin n) = n := Fintype.card_fin n
  set q := (MvPolynomial.esymmAlgEquiv (Fin n) F hcard).symm ⟨f, hf⟩
  refine ⟨q, ?_⟩
  have hfq : f = (MvPolynomial.aeval
    (fun i : Fin n => MvPolynomial.esymm (Fin n) F (i.val + 1))) q := by
    have h1 : ((MvPolynomial.esymmAlgEquiv (Fin n) F hcard) q).val = f := by
      simp [q, AlgEquiv.apply_symm_apply]
    rw [← h1]
    change ((MvPolynomial.esymmAlgHom (Fin n) F n) q).val = _
    exact MvPolynomial.esymmAlgHom_apply (σ := Fin n) q
  suffices h : ∀ i : Fin n,
    MvPolynomial.eval α (MvPolynomial.esymm (Fin n) F (i.val + 1)) =
      (-1 : F) ^ (i.val + 1) * P.coeff (n - (i.val + 1)) by
    rw [hfq]
    have key : (MvPolynomial.eval α).comp (MvPolynomial.aeval
      (fun i : Fin n => MvPolynomial.esymm (Fin n) F (i.val + 1))).toRingHom =
      MvPolynomial.eval
        (fun i : Fin n => (-1 : F) ^ (i.val + 1) * P.coeff (n - (i.val + 1))) := by
      apply MvPolynomial.ringHom_ext
      · intro r; simp [MvPolynomial.eval_C]
      · intro i
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          MvPolynomial.aeval_X, MvPolynomial.eval_X]
        exact h i
    exact RingHom.congr_fun key q
  intro i
  have hesymm : MvPolynomial.eval α (MvPolynomial.esymm (Fin n) F (i.val + 1)) =
    (Finset.univ.val.map α).esymm (i.val + 1) := by
    have := MvPolynomial.aeval_esymm_eq_multiset_esymm (Fin n) F (i.val + 1) α
    rwa [MvPolynomial.aeval_def] at this
  rw [hesymm]
  have hroots : P.roots = Finset.univ.val.map α := by
    rw [hα, Finset.prod_eq_multiset_prod]
    conv_lhs =>
      rw [show Multiset.map (fun i => Polynomial.X - Polynomial.C (α i)) Finset.univ.val =
        Multiset.map (fun a => Polynomial.X - Polynomial.C a) (Finset.univ.val.map α) from by
          rw [Multiset.map_map]; rfl]
    exact Polynomial.roots_multiset_prod_X_sub_C _
  rw [← hroots]
  have hi_le : n - (i.val + 1) ≤ P.natDegree := by omega
  have hvieta := Polynomial.coeff_eq_esymm_roots_of_splits hsplit hi_le
  rw [hP.leadingCoeff, one_mul] at hvieta
  have hsub : P.natDegree - (n - (i.val + 1)) = i.val + 1 := by omega
  rw [hsub] at hvieta
  rw [hvieta, ← mul_assoc, ← pow_add]
  simp

end GaloisTheory

namespace GaloisTheory

/--
[all_minpoly_split_in_splitting_field](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/GaloisTheory.lean)
-/
@[path]
lemma all_minpoly_split_in_splitting_field
  [Field F]
  [Field E]
  [Algebra F E]
  [Field F]
  {p : Polynomial F}
  {α : p.SplittingField} :
-- imply
  (Polynomial.map (algebraMap F p.SplittingField) (minpoly F α)).Splits := by
-- proof
  haveI : Normal F p.SplittingField := Polynomial.SplittingField.instNormal p
  exact Normal.splits inferInstance α

end GaloisTheory

namespace GaloisTheory

/--
[s5_not_solvable_and_a5_simple](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/GaloisTheory.lean)
-/
@[path]
lemma s5_not_solvable_and_a5_simple
  [Field F]
  [Field E]
  [Algebra F E] :
-- imply
  ¬IsSolvable (Equiv.Perm (Fin 5)) ∧ IsSimpleGroup (alternatingGroup (Fin 5)) :=
-- proof
  ⟨Equiv.Perm.fin_5_not_solvable, alternatingGroup.isSimpleGroup_five⟩

end GaloisTheory

namespace GaloisTheory

/--
[symmetric_group_not_solvable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/GaloisTheory.lean)
-/
@[path]
lemma symmetric_group_not_solvable
  [Field F]
  [Field E]
  [Algebra F E]
  {n : ℕ}
-- given
  (hn : 5 ≤ n) :
-- imply
  ¬IsSolvable (Equiv.Perm (Fin n)) := by
-- proof
  apply Equiv.Perm.not_solvable
  rw [Cardinal.mk_fin]
  exact_mod_cast hn

end GaloisTheory

namespace GaloisTheory

/--
[not_solvableByRad_of_gal_iso_S5](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/GaloisTheory.lean)
-/
@[path]
lemma not_solvableByRad_of_gal_iso_S5
  [Field F]
  [Field E]
  [Algebra F E]
  [Field F]
  [Field E]
  [Algebra F E]
  {p : F[X]}
  {x : E}
-- given
  (hp : Irreducible p)
  (hiso : p.Gal ≃* Equiv.Perm (Fin 5))
  (hpx : aeval x p = 0) :
-- imply
  x ∉ solvableByRad F E := by
-- proof
  intro hx
  have hsol : IsSolvable p.Gal := isSolvable_gal_of_irreducible hx hp hpx
  have : IsSolvable (Equiv.Perm (Fin 5)) := by
    haveI := hsol
    exact solvable_of_surjective (f := hiso.toMonoidHom) hiso.surjective
  exact Equiv.Perm.fin_5_not_solvable this

end GaloisTheory


-- created on 2026-10-23
