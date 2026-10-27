import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.BertiniDegree
open MvPolynomial Finset


/--
[pderiv_X_pow](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BertiniDegree.lean)
-/
@[path]
lemma pderiv_X_pow
  [CommRing k]
  [DecidableEq σ]
  {i j : σ}
  {d : ℕ} :
-- imply
  (pderiv (R := k) i) ((X j : MvPolynomial σ k) ^ d) = if i = j then (d : MvPolynomial σ k) * X j ^ (d - 1) else 0 := by
-- proof
  rw [Derivation.leibniz_pow, pderiv_X, nsmul_eq_mul]
  split
  · next h => subst h; simp [Pi.single_eq_same]
  · next h => simp [Pi.single, Function.update, Ne.symm h]

/--
[homogeneous_euler_vanishing](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BertiniDegree.lean)
-/
@[path]
lemma homogeneous_euler_vanishing
  [Field k]
  {n : ℕ}
  {f : MvPolynomial (Fin (n + 1)) k}
  {d : ℕ}
  {x : Fin (n + 1) → k}
-- given
  (hf : f.IsHomogeneous d)
  (hpd : ∀ i : Fin (n + 1), MvPolynomial.eval x (pderiv i f) = 0) :
-- imply
  (d : k) * MvPolynomial.eval x f = 0 := by
-- proof
  have euler := hf.sum_X_mul_pderiv
  have h := congr_arg (MvPolynomial.eval x) euler
  simp [map_sum, map_mul, eval_X] at h
  rw [Finset.sum_eq_zero] at h
  · simpa [nsmul_eq_mul] using h
  · intro i _
    simp [hpd i]

/--
[homogeneous_singular_implies_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BertiniDegree.lean)
-/
@[path]
lemma homogeneous_singular_implies_zero
  [Field k]
  {n : ℕ}
  {f : MvPolynomial (Fin (n + 1)) k}
  {d : ℕ}
  {x : Fin (n + 1) → k}
-- given
  (hf : f.IsHomogeneous d)
  (hd : (d : k) ≠ 0)
  (hpd : ∀ i : Fin (n + 1), MvPolynomial.eval x (pderiv i f) = 0) :
-- imply
  MvPolynomial.eval x f = 0 := by
-- proof
  have h := homogeneous_euler_vanishing f d hf x hpd
  exact (mul_eq_zero.mp h).resolve_left hd

/--
[singular_zero_iff_partials_vanish](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BertiniDegree.lean)
-/
@[path]
lemma singular_zero_iff_partials_vanish
  [Field k]
  {n : ℕ}
  {f : MvPolynomial (Fin (n + 1)) k}
  {d : ℕ}
  {x : Fin (n + 1) → k}
-- given
  (hf : f.IsHomogeneous d)
  (hd : (d : k) ≠ 0) :
-- imply
  IsSingularZero f x ↔ ∀ i : Fin (n + 1), MvPolynomial.eval x (pderiv i f) = 0 := by
-- proof
  constructor
  · exact fun ⟨_, h⟩ => h
  · intro hpd
    exact ⟨homogeneous_singular_implies_zero f d hf hd x hpd, hpd⟩

/--
[fermatPoly_isHomogeneous](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BertiniDegree.lean)
-/
@[path]
lemma fermatPoly_isHomogeneous
  {k : Type*}
  [CommSemiring k]
  {n d : ℕ} :
-- imply
  (fermatPoly k n d).IsHomogeneous d := by
-- proof
  apply IsHomogeneous.sum
  intro i _
  have h := (isHomogeneous_X k i).pow d
  simp [one_mul] at h
  exact h

/--
[pderiv_fermatPoly](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BertiniDegree.lean)
-/
@[path]
lemma pderiv_fermatPoly
  [CommRing k]
  {n : ℕ}
  {d : ℕ}
  {i : Fin (n + 1)} :
-- imply
  (pderiv i) (fermatPoly k n d) = (d : MvPolynomial (Fin (n + 1)) k) * X i ^ (d - 1) := by
-- proof
  simp only [fermatPoly, map_sum, pderiv_X_pow]
  simp [Finset.mem_univ]

/--
[fermat_no_nontrivial_singular](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BertiniDegree.lean)
-/
@[path]
lemma fermat_no_nontrivial_singular
  [Field k]
  {n : ℕ}
  {d : ℕ}
  {x : Fin (n + 1) → k}
-- given
  (hd : (d : k) ≠ 0)
  (hd2 : 2 ≤ d)
  (hx : x ≠ 0)
  (hpd : ∀ i, MvPolynomial.eval x (pderiv i (fermatPoly k n d)) = 0) :
-- imply
  False := by
-- proof
  have hxi : ∀ i, x i = 0 := by
    intro i
    have hi := hpd i
    rw [pderiv_fermatPoly] at hi
    rw [map_mul, map_natCast, map_pow, eval_X] at hi
    obtain h | h := mul_eq_zero.mp hi
    · exact absurd h hd
    · exact pow_eq_zero_iff (by omega : d - 1 ≠ 0) |>.mp h
  exact hx (funext hxi)

/--
[discriminant_locus_proper](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BertiniDegree.lean)
-/
@[path]
lemma discriminant_locus_proper
  [Field k]
  {n : ℕ}
  {d : ℕ}
-- given
  (hd : (d : k) ≠ 0)
  (hd2 : 2 ≤ d) :
-- imply
  ¬∀ (f : MvPolynomial (Fin (n + 1)) k), f.IsHomogeneous d → ∃ x : Fin (n + 1) → k, x ≠ 0 ∧ IsSingularZero f x := by
-- proof
  intro hall
  obtain ⟨x, hx, _, hpd⟩ := hall (fermatPoly k n d) (fermatPoly_isHomogeneous k n d)
  exact fermat_no_nontrivial_singular hd hd2 x hx hpd

/--
[bertini_smooth_exists](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BertiniDegree.lean)
-/
@[path]
lemma bertini_smooth_exists
  [Field k]
  {n : ℕ}
  {d : ℕ}
-- given
  (hd : (d : k) ≠ 0)
  (hd2 : 2 ≤ d) :
-- imply
  ∃ f : MvPolynomial (Fin (n + 1)) k, f.IsHomogeneous d ∧ ∀ x : Fin (n + 1) → k, x ≠ 0 → ¬∀ i, MvPolynomial.eval x (pderiv i f) = 0 :=
-- proof
  ⟨fermatPoly k n d, fermatPoly_isHomogeneous k n d,
    fun x hx hpd => fermat_no_nontrivial_singular hd hd2 x hx hpd⟩

/--
[smooth_hypersurface_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BertiniDegree.lean)
-/
@[path]
lemma smooth_hypersurface_nonempty
  [Field k]
  {n : ℕ}
  {d : ℕ}
-- given
  (hd : (d : k) ≠ 0)
  (hd2 : 2 ≤ d) :
-- imply
  ∃ f : MvPolynomial (Fin (n + 1)) k, f.IsHomogeneous d ∧ ∀ x : Fin (n + 1) → k, x ≠ 0 → ¬IsSingularZero f x := by
-- proof
  obtain ⟨f, hfhom, hfsmooth⟩ := bertini_smooth_exists hd hd2
  exact ⟨f, hfhom, fun x hx hsing => hfsmooth x hx hsing.2⟩

/--
[isSingularZero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BertiniDegree.lean)
-/
@[path]
lemma isSingularZero_iff
  [Field k]
  {n : ℕ}
  {f : MvPolynomial (Fin (n + 1)) k}
  {x : Fin (n + 1) → k} :
-- imply
  IsSingularZero f x ↔ MvPolynomial.eval x f = 0 ∧ ∀ i : Fin (n + 1), MvPolynomial.eval x (pderiv i f) = 0 :=
-- proof
  Iff.rfl

/--
[discriminantLocus_ne_univ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BertiniDegree.lean)
-/
@[path]
lemma discriminantLocus_ne_univ
  {k : Type*}
  [Field k]
  {n d : ℕ}
-- given
  (hd : (d : k) ≠ 0)
  (hd2 : 2 ≤ d) :
-- imply
  discriminantLocus k n d ≠ Set.univ := by
-- proof
  intro h
  have := Set.mem_univ (fermatPoly k n d)
  rw [← h] at this
  obtain ⟨_, x, hx, _, hpd⟩ := this
  exact fermat_no_nontrivial_singular hd hd2 x hx hpd

/--
[vanishing_at_point_subspace](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BertiniDegree.lean)
-/
@[path]
lemma vanishing_at_point_subspace
  [Field k]
  {n : ℕ}
  {x : Fin (n + 1) → k} :
-- imply
  ∀ (f g : MvPolynomial (Fin (n + 1)) k) (c : k), MvPolynomial.eval x f = 0 → MvPolynomial.eval x g = 0 → MvPolynomial.eval x (f + c • g) = 0 := by
-- proof
  intro f g c hf hg
  simp [map_add, hf, hg]

/--
[singular_at_point_linear](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BertiniDegree.lean)
-/
@[path]
lemma singular_at_point_linear
  [Field k]
  {n : ℕ}
  {x : Fin (n + 1) → k}
  {f g : MvPolynomial (Fin (n + 1)) k}
  {c : k} :
-- imply
  IsSingularZero f x → IsSingularZero g x → IsSingularZero (f + c • g) x := by
-- proof
  intro ⟨hf, hpf⟩ ⟨hg, hpg⟩
  exact ⟨by simp [map_add, hf, hg],
    fun i => by simp [map_add, hpf i, hpg i]⟩

/--
[bertini_generic_smooth](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BertiniDegree.lean)
-/
@[path]
lemma bertini_generic_smooth
  [Field k]
  {n d : ℕ}
-- given
  (hd : (d : k) ≠ 0)
  (hd2 : 2 ≤ d) :
-- imply
  (∃ f : MvPolynomial (Fin (n + 1)) k, f.IsHomogeneous d ∧ ∀ x, x ≠ 0 → ¬IsSingularZero f x) ∧ (∀ x : Fin (n + 1) → k, ∀ f g : MvPolynomial (Fin (n + 1)) k, ∀ c : k, IsSingularZero f x → IsSingularZero g x → IsSingularZero (f + c • g) x) := by
-- proof
  exact ⟨⟨fermatPoly k n d, fermatPoly_isHomogeneous k n d,
    fun x hx hsing => fermat_no_nontrivial_singular hd hd2 x hx hsing.2⟩,
    fun x f g c => singular_at_point_linear x f g c⟩
section DegreeAdditivity

/--
[length_additive_submodule](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BertiniDegree.lean)
-/
@[path]
lemma length_additive_submodule
  [Ring R]
  [AddCommGroup M]
  [Module R M]
  {N : Submodule R M} :
-- imply
  Module.length R M = Module.length R N + Module.length R (M ⧸ N) :=
-- proof
  Module.length_eq_add_of_exact N.subtype N.mkQ
    (Submodule.subtype_injective N) (Submodule.mkQ_surjective N)
    (LinearMap.exact_subtype_mkQ N)

/--
[length_additive_exact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BertiniDegree.lean)
-/
@[path]
lemma length_additive_exact
  [Ring R]
  [AddCommGroup N]
  [AddCommGroup M]
  [AddCommGroup P]
  [Module R N]
  [Module R M]
  [Module R P]
  {f : N →ₗ[R] M}
  {g : M →ₗ[R] P}
-- given
  (hf : Function.Injective f)
  (hg : Function.Surjective g)
  (hex : Function.Exact f g) :
-- imply
  Module.length R M = Module.length R N + Module.length R P :=
-- proof
  Module.length_eq_add_of_exact f g hf hg hex

/--
[length_finite_of_artinian_noetherian](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BertiniDegree.lean)
-/
@[path]
lemma length_finite_of_artinian_noetherian
  [Ring R]
  [AddCommGroup M]
  [Module R M]
  [IsArtinian R M]
  [IsNoetherian R M] :
-- imply
  Module.length R M ≠ ⊤ :=
-- proof
  Module.length_ne_top
end DegreeAdditivity
section K0DegreeMap
variable (R : Type*) [Ring R]

/--
[degree_map_respects_iso](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BertiniDegree.lean)
-/
@[path]
lemma degree_map_respects_iso
  {R : Type*}
  [Ring R]
  [AddCommGroup M]
  [Module R M]
  [AddCommGroup N]
  [Module R N]
  {e : M ≃ₗ[R] N} :
-- imply
  Module.length R M = Module.length R N :=
-- proof
  e.length_eq

/--
[degree_map_wellDefined_on_K0](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BertiniDegree.lean)
-/
@[path]
lemma degree_map_wellDefined_on_K0
  {R : Type*}
  [Ring R]
  [AddCommGroup N]
  [AddCommGroup M]
  [AddCommGroup P]
  [Module R N]
  [Module R M]
  [Module R P]
  {f : N →ₗ[R] M}
  {g : M →ₗ[R] P}
-- given
  (hf : Function.Injective f)
  (hg : Function.Surjective g)
  (hex : Function.Exact f g) :
-- imply
  Module.length R M = Module.length R N + Module.length R P :=
-- proof
  Module.length_eq_add_of_exact f g hf hg hex

/--
[degree_map_additive_prod](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BertiniDegree.lean)
-/
@[path]
lemma degree_map_additive_prod
  {R : Type*}
  [Ring R]
  {M N : Type*}
  [AddCommGroup M]
  [Module R M]
  [AddCommGroup N]
  [Module R N] :
-- imply
  Module.length R (M × N) = Module.length R M + Module.length R N :=
-- proof
  Module.length_prod R M N

/--
[degree_map_finite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BertiniDegree.lean)
-/
@[path]
lemma degree_map_finite
  {R : Type*}
  [Ring R]
  [AddCommGroup M]
  [Module R M]
  [IsArtinian R M]
  [IsNoetherian R M] :
-- imply
  Module.length R M ≠ ⊤ :=
-- proof
  Module.length_ne_top

/--
[degree_map_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BertiniDegree.lean)
-/
@[path]
lemma degree_map_zero
  {R : Type*}
  [Ring R] :
-- imply
  Module.length R (PUnit : Type) = 0 := by
-- proof
  have : Subsingleton PUnit := inferInstance
  exact Module.length_eq_zero

/--
[degree_map_simple](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BertiniDegree.lean)
-/
@[path]
lemma degree_map_simple
  {R : Type*}
  [Ring R]
  {M : Type*}
  [AddCommGroup M]
  [Module R M]
  [IsSimpleModule R M] :
-- imply
  Module.length R M = 1 :=
-- proof
  Module.length_eq_one R M
end K0DegreeMap


-- created on 2026-10-23
