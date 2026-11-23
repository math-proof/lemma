module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.RingTheory.Ideal.Span
public import Notation.WeierstrassCurve_ProjModel_AddFormulas

public noncomputable section

set_option Elab.async false

section MEGA_KwLRChordAddFormulas_lean
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedSimpArgs false

noncomputable section

open MvPolynomial WeierstrassCurve

namespace WeierstrassProjModel

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

open scoped WeierstrassCurve_ProjModel_AddFormulas


public theorem kw_lrAdd_isHomog_C_mul {σ : Type*} {n : ℕ} (r : R)
    {q : MvPolynomial σ R} (hq : q.IsHomogeneous n) : (C r * q).IsHomogeneous n :=
  Nat.zero_add n ▸ (isHomogeneous_C _ r).mul hq


public theorem kw_lrAdd_c₂₁_isHomogeneous : (c₂₁).IsHomogeneous 3 := by
  unfold kw_lrAdd_c₂₁

  repeat' first
    | with_reducible apply IsHomogeneous.add | with_reducible apply IsHomogeneous.sub
    | with_reducible apply IsHomogeneous.neg
    | with_reducible exact isHomogeneous_C _ _
    | with_reducible exact isHomogeneous_X _ _
    | with_reducible exact (isHomogeneous_X _ _).pow _
    | with_reducible refine IsHomogeneous.mul ?_ (isHomogeneous_X _ _)
    | with_reducible refine IsHomogeneous.mul ?_ ((isHomogeneous_X _ _).pow _)
    | with_reducible refine kw_lrAdd_isHomog_C_mul _ ?_


public theorem kw_lrAdd_c₁₂_isHomogeneous : (c₁₂).IsHomogeneous 3 := by
  unfold kw_lrAdd_c₁₂

  repeat' first
    | with_reducible apply IsHomogeneous.add | with_reducible apply IsHomogeneous.sub
    | with_reducible apply IsHomogeneous.neg
    | with_reducible exact isHomogeneous_C _ _
    | with_reducible exact isHomogeneous_X _ _
    | with_reducible exact (isHomogeneous_X _ _).pow _
    | with_reducible refine IsHomogeneous.mul ?_ (isHomogeneous_X _ _)
    | with_reducible refine IsHomogeneous.mul ?_ ((isHomogeneous_X _ _).pow _)
    | with_reducible refine kw_lrAdd_isHomog_C_mul _ ?_


public theorem kw_lrAdd_X_isHomogeneous : (kw_lrAdd_X W).IsHomogeneous 4 := by
  show ((c₁₂) * (Xl 0) - (c₂₁) * (Xr 0)).IsHomogeneous 4
  exact ((kw_lrAdd_c₁₂_isHomogeneous W).mul (isHomogeneous_X _ _)).sub
    ((kw_lrAdd_c₂₁_isHomogeneous W).mul (isHomogeneous_X _ _))


public theorem kw_lrAdd_Z_isHomogeneous : (kw_lrAdd_Z W).IsHomogeneous 4 := by
  show ((c₁₂) * (Xl 2) - (c₂₁) * (Xr 2)).IsHomogeneous 4
  exact ((kw_lrAdd_c₁₂_isHomogeneous W).mul (isHomogeneous_X _ _)).sub
    ((kw_lrAdd_c₂₁_isHomogeneous W).mul (isHomogeneous_X _ _))


public theorem kw_lrAdd_Y_isHomogeneous : (kw_lrAdd_Y W).IsHomogeneous 4 := by
  unfold kw_lrAdd_Y
  have hX : (kw_lrAdd_starX W).IsHomogeneous 4 := kw_lrAdd_X_isHomogeneous W
  have hZ : (kw_lrAdd_starZ W).IsHomogeneous 4 := kw_lrAdd_Z_isHomogeneous W
  have hY : (kw_lrAdd_starY W).IsHomogeneous 4 :=
    ((kw_lrAdd_c₁₂_isHomogeneous W).mul (isHomogeneous_X _ _)).sub
      ((kw_lrAdd_c₂₁_isHomogeneous W).mul (isHomogeneous_X _ _))
  exact (hY.neg.sub ((isHomogeneous_C _ _).mul hX)).sub ((isHomogeneous_C _ _).mul hZ)

section OnCurve


public theorem kw_lrAdd_spec_rename (p : P₆) : σ (ι p) = p := by
  show aeval (Sum.elim X ![c₁₂, -c₂₁]) (rename Sum.inl p) = p
  rw [aeval_rename, Sum.elim_comp_inl]
  exact congrFun (congrArg DFunLike.coe aeval_X_left) p


public theorem kw_lrAdd_spec_s : σ 𝓈 = c₁₂ := by
  simp only [kw_lrAdd_spec, aeval_X, Sum.elim_inr, Matrix.cons_val_zero]


public theorem kw_lrAdd_spec_t : σ 𝓉 = -c₂₁ := by
  simp only [kw_lrAdd_spec, aeval_X, Sum.elim_inr, Matrix.cons_val_one, Matrix.cons_val_zero]


public theorem kw_lrAdd_chordCubic :
    aeval (fun i => 𝓈 * ι (Xl i) + 𝓉 * ι (Xr i)) W.toProjective.polynomial
      = 𝓈^3 * ι WP₁ + 𝓈^2 * 𝓉 * ι c₂₁ + 𝓈 * 𝓉^2 * ι c₁₂ + 𝓉^3 * ι WP₂ := by
  simp only [kw_lrAdd_WP₁, kw_lrAdd_WP₂, kw_lrAdd_c₂₁, kw_lrAdd_c₁₂,
    WeierstrassCurve.Projective.polynomial, WeierstrassCurve.toProjective,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, rename_X, rename_C,
    aeval_X, aeval_C, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, MvPolynomial.algebraMap_eq]
  ring


public theorem kw_lrAdd_negInvariant {S : Type u} [CommRing S] [Algebra R S] (x y z : S) :
    aeval ![x, -y - algebraMap R S W.a₁ * x - algebraMap R S W.a₃ * z, z]
        W.toProjective.polynomial
      = aeval ![x, y, z] W.toProjective.polynomial := by
  simp only [WeierstrassCurve.Projective.polynomial, WeierstrassCurve.toProjective,
    map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  ring


public theorem kw_lrAdd_star_onCurve :
    aeval ![kw_lrAdd_starX W, kw_lrAdd_starY W, kw_lrAdd_starZ W]
        W.toProjective.polynomial
      = c₁₂^3 * WP₁ - c₂₁^3 * WP₂ := by

  have hcomp : (σ).comp (aeval (fun i => 𝓈 * ι (Xl i) + 𝓉 * ι (Xr i)))
      = (aeval ![kw_lrAdd_starX W, kw_lrAdd_starY W, kw_lrAdd_starZ W]
          : MvPolynomial (Fin 3) R →ₐ[R] P₆) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;>
      simp only [AlgHom.comp_apply, map_add, map_mul, aeval_X, Fin.isValue,
        kw_lrAdd_spec_rename, kw_lrAdd_spec_s, kw_lrAdd_spec_t,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons,
        kw_lrAdd_starX, kw_lrAdd_starY, kw_lrAdd_starZ, neg_mul, ← sub_eq_add_neg] <;>
      rfl
  rw [show (aeval ![kw_lrAdd_starX W, kw_lrAdd_starY W, kw_lrAdd_starZ W]
        : MvPolynomial (Fin 3) R →ₐ[R] P₆) W.toProjective.polynomial
      = σ (aeval (fun i => 𝓈 * ι (Xl i) + 𝓉 * ι (Xr i)) W.toProjective.polynomial)
    from by rw [← AlgHom.comp_apply, hcomp], kw_lrAdd_chordCubic]

  simp only [map_add, map_mul, map_pow, kw_lrAdd_spec_rename,
    kw_lrAdd_spec_s, kw_lrAdd_spec_t]
  ring


public theorem kw_lrAdd_onCurve :
    aeval ![kw_lrAdd_X W, kw_lrAdd_Y W, kw_lrAdd_Z W] W.toProjective.polynomial
      = c₁₂^3 * WP₁ - c₂₁^3 * WP₂ := by
  have hneg : aeval ![kw_lrAdd_X W, kw_lrAdd_Y W, kw_lrAdd_Z W] W.toProjective.polynomial
      = aeval ![kw_lrAdd_starX W, kw_lrAdd_starY W, kw_lrAdd_starZ W]
          W.toProjective.polynomial := by
    have := kw_lrAdd_negInvariant W (S := P₆)
      (kw_lrAdd_starX W) (kw_lrAdd_starY W) (kw_lrAdd_starZ W)
    simp only [kw_lrAdd_X, kw_lrAdd_Y, kw_lrAdd_Z, algebraMap_eq] at this ⊢
    exact this
  rw [hneg, kw_lrAdd_star_onCurve]


public theorem kw_lrAdd_onCurve_mem_span :
    aeval ![kw_lrAdd_X W, kw_lrAdd_Y W, kw_lrAdd_Z W] W.toProjective.polynomial
      ∈ Ideal.span {WP₁, WP₂} := by
  rw [kw_lrAdd_onCurve]
  exact sub_mem (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert _ _)))
    (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))))

end OnCurve

end WeierstrassProjModel

end

end MEGA_KwLRChordAddFormulas_lean

section MEGA_KwLRSymAddFormulas_lean
set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option linter.unusedSimpArgs false

noncomputable section

open MvPolynomial WeierstrassCurve

namespace WeierstrassProjModel

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

open scoped WeierstrassCurve_ProjModel_AddFormulas


public theorem kw_lrSym_X_isHomogeneous : (kw_lrSym_X W).IsHomogeneous 4 := by
  unfold kw_lrSym_X
  repeat' first
    | with_reducible apply IsHomogeneous.add
    | with_reducible exact isHomogeneous_C _ _
    | with_reducible refine IsHomogeneous.mul ?_ (isHomogeneous_X _ _)
    | with_reducible refine IsHomogeneous.mul ?_ ((isHomogeneous_X _ _).pow _)


public theorem kw_lrSym_Y_isHomogeneous : (kw_lrSym_Y W).IsHomogeneous 4 := by
  unfold kw_lrSym_Y
  repeat' first
    | with_reducible apply IsHomogeneous.add
    | with_reducible exact isHomogeneous_C _ _
    | with_reducible refine IsHomogeneous.mul ?_ (isHomogeneous_X _ _)
    | with_reducible refine IsHomogeneous.mul ?_ ((isHomogeneous_X _ _).pow _)


public theorem kw_lrSym_Z_isHomogeneous : (kw_lrSym_Z W).IsHomogeneous 4 := by
  unfold kw_lrSym_Z
  repeat' first
    | with_reducible apply IsHomogeneous.add
    | with_reducible exact isHomogeneous_C _ _
    | with_reducible refine IsHomogeneous.mul ?_ (isHomogeneous_X _ _)
    | with_reducible refine IsHomogeneous.mul ?_ ((isHomogeneous_X _ _).pow _)

section OnCurve

end OnCurve

section Minors


public theorem kw_lrSym_minor_XZ :
    kw_lrSym_X W * kw_lrAdd_Z W - kw_lrSym_Z W * kw_lrAdd_X W
      = kw_lrSym_pXZ W * WP₁ + kw_lrSym_qXZ W * WP₂ := by
  simp only [kw_lrSym_X, kw_lrSym_Z, kw_lrAdd_X, kw_lrAdd_Y, kw_lrAdd_Z,
    kw_lrAdd_starX, kw_lrAdd_starY, kw_lrAdd_starZ, kw_lrAdd_c₂₁, kw_lrAdd_c₁₂,
    kw_lrSym_pXZ, kw_lrSym_qXZ, kw_lrAdd_WP₁, kw_lrAdd_WP₂,
    WeierstrassCurve.Projective.polynomial, WeierstrassCurve.toProjective,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, rename_X, rename_C,
    MvPolynomial.algebraMap_eq]
  ring


public theorem kw_lrSym_minor_XZ_mem_span :
    kw_lrSym_X W * kw_lrAdd_Z W - kw_lrSym_Z W * kw_lrAdd_X W
      ∈ Ideal.span {WP₁, WP₂} := by
  rw [kw_lrSym_minor_XZ]
  exact add_mem (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert _ _)))
    (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))))


public theorem kw_lrSym_minor_YZ :
    kw_lrSym_Y W * kw_lrAdd_Z W - kw_lrSym_Z W * kw_lrAdd_Y W
      = kw_lrSym_pYZ W * WP₁ + kw_lrSym_qYZ W * WP₂ := by
  simp only [kw_lrSym_Y, kw_lrSym_Z, kw_lrAdd_X, kw_lrAdd_Y, kw_lrAdd_Z,
    kw_lrAdd_starX, kw_lrAdd_starY, kw_lrAdd_starZ, kw_lrAdd_c₂₁, kw_lrAdd_c₁₂,
    kw_lrSym_pYZ, kw_lrSym_qYZ, kw_lrAdd_WP₁, kw_lrAdd_WP₂,
    WeierstrassCurve.Projective.polynomial, WeierstrassCurve.toProjective,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, rename_X, rename_C,
    MvPolynomial.algebraMap_eq]
  ring


public theorem kw_lrSym_minor_YZ_mem_span :
    kw_lrSym_Y W * kw_lrAdd_Z W - kw_lrSym_Z W * kw_lrAdd_Y W
      ∈ Ideal.span {WP₁, WP₂} := by
  rw [kw_lrSym_minor_YZ]
  exact add_mem (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert _ _)))
    (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))))

end Minors

section Diag

