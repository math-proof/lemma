import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicTopologyI.code.Section20
open TensorProduct HomologyWithCoefficients
open EilenbergSteenrod TensorProduct


namespace TensorProduct

/--
[mk_isBilinearMap](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section20.lean)
-/
@[path]
lemma mk_isBilinearMap
  [CommSemiring R]
  [AddCommMonoid M]
  [AddCommMonoid N]
  [AddCommMonoid P]
  [Module R M]
  [Module R N]
  [Module R P] :
-- imply
  IsBilinearMap R (fun (m : M) (n : N) => m ⊗ₜ[R] n) where add_left m₁ m₂ n := by
-- proof
simp [add_tmul]
  smul_left r m n := by simp [smul_tmul']
  add_right m n₁ n₂ := by simp [tmul_add]
  smul_right r m n := by simp [tmul_smul]

end TensorProduct

namespace TensorProduct

/--
[lift_tmul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section20.lean)
-/
@[path]
lemma lift_tmul
  [CommSemiring R]
  [AddCommMonoid M]
  [AddCommMonoid N]
  [AddCommMonoid P]
  [Module R M]
  [Module R N]
  [Module R P]
  {β : M →ₗ[R] N →ₗ[R] P}
  {m : M}
  {n : N} :
-- imply
  TensorProduct.lift β (m ⊗ₜ[R] n) = β m n :=
-- proof
  TensorProduct.lift.tmul m n

end TensorProduct

namespace TensorProduct

/--
[lift_unique](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section20.lean)
-/
@[path]
lemma lift_unique
  [CommSemiring R]
  [AddCommMonoid M]
  [AddCommMonoid N]
  [AddCommMonoid P]
  [Module R M]
  [Module R N]
  [Module R P]
  {β : M →ₗ[R] N →ₗ[R] P}
  {g : M ⊗[R] N →ₗ[R] P}
-- given
  (hg : ∀ (m : M) (n : N), g (m ⊗ₜ[R] n) = β m n) :
-- imply
  g = TensorProduct.lift β :=
-- proof
  TensorProduct.lift.unique hg

end TensorProduct

namespace TensorProduct

/--
[construction](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section20.lean)
-/
@[path]
lemma construction
  [CommSemiring R]
  [AddCommMonoid M]
  [AddCommMonoid N]
  [AddCommMonoid P]
  [Module R M]
  [Module R N]
  [Module R P] :
-- imply
  M ⊗[R] N = (addConGen (TensorProduct.Eqv R M N)).Quotient :=
-- proof
  rfl

end TensorProduct

namespace TensorProduct

/--
[induction](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section20.lean)
-/
@[path]
lemma induction
  [CommSemiring R]
  [AddCommMonoid M]
  [AddCommMonoid N]
  [AddCommMonoid P]
  [Module R M]
  [Module R N]
  [Module R P]
  {zero : C 0}
  {t : M ⊗[R] N}
-- given
  (C : M ⊗[R] N → Prop)
  (tmul : ∀ m n, C (m ⊗ₜ[R] n))
  (add : ∀ x y, C x → C y → C (x + y)) :
-- imply
  C t :=
-- proof
  TensorProduct.induction_on t zero tmul add
end TensorProduct
namespace HomologyWithCoefficients
open EilenbergSteenrod TensorProduct


namespace HomologyWithCoefficients

/--
[coproduct_lTensor](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section20.lean)
-/
@[path]
lemma coproduct_lTensor
  {M : Type}
  [AddCommGroup M]
  {n : ℤ}
  {ι : Type}
  [DecidableEq ι]
  {X : ι → Type}
  [∀ i, TopologicalSpace (X i)]
-- given
  (h : HomologyTheory.{0})
  (hbij : Function.Bijective (DirectSum.toAddMonoid (β := fun i => h.H n (TopPair.ofSpace (X i))) (fun i => h.map n (coproductInclusion ι X i)))) :
-- imply
  Function.Bijective (DirectSum.toAddMonoid (β := fun i => TensorProduct ℤ (h.H n (TopPair.ofSpace (X i))) M) (fun i => (TensorProduct.map (h.map n (coproductInclusion ι X i)).toIntLinearMap (LinearMap.id : M →ₗ[ℤ] M)).toAddMonoidHom)) := by
-- proof
  have htensor_bij : Function.Bijective
    (TensorProduct.map (DirectSum.toAddMonoid (β := fun i => h.H n (TopPair.ofSpace (X i)))
      (fun i => h.map n (coproductInclusion ι X i))).toIntLinearMap
      (LinearMap.id : M →ₗ[ℤ] M)) :=
    TensorProduct.map_bijective hbij Function.bijective_id
  let A := fun i => h.H n (TopPair.ofSpace (X i))
  let B := h.H n (TopPair.ofSpace (Sigma X))
  let φ := fun i => h.map n (coproductInclusion ι X i)
  let f := DirectSum.toAddMonoid (β := fun i => TensorProduct ℤ (A i) M)
    (fun i => (TensorProduct.map (φ i).toIntLinearMap LinearMap.id).toAddMonoidHom)
  let g := (TensorProduct.map (DirectSum.toAddMonoid φ).toIntLinearMap
    (LinearMap.id : M →ₗ[ℤ] M)).comp
    (TensorProduct.directSumLeft ℤ (S := ℤ) A M).symm.toLinearMap
  suffices heq : (f : DirectSum ι (fun i => TensorProduct ℤ (A i) M) →+ TensorProduct ℤ B M) =
    g.toAddMonoidHom by
    rw [show (⇑f) = (⇑g.toAddMonoidHom) from congr_arg DFunLike.coe heq]
    exact htensor_bij.comp (TensorProduct.directSumLeft ℤ (S := ℤ) A M).symm.bijective
  ext i t
  induction t using TensorProduct.induction_on with
  | zero => simp [f, g, map_zero]
  | tmul a m =>
    simp only [f, g, AddMonoidHom.comp_apply, DirectSum.toAddMonoid_of,
      LinearMap.toAddMonoidHom_coe, LinearMap.comp_apply,
      TensorProduct.map_tmul, LinearMap.id_coe, id_eq]
    erw [TensorProduct.directSumLeft_symm_lof_tmul ℤ ℤ (M₁ := A) (M₂' := M) i a m,
      TensorProduct.map_tmul]
    simp only [LinearMap.id_coe, id_eq]
    congr 1
    show (φ i) a = (DirectSum.toAddMonoid φ) (DirectSum.of A i a)
    rw [DirectSum.toAddMonoid_of]
  | add x y hx hy => simp [map_add, hx, hy]
/-- (Proposition 20.11) Homology with coefficients in an abelian group $M$ defines a homology
theory $H_*(X, A; M) := H_*(X, A) \otimes_{\mathbf{Z}} M$ satisfying the Eilenberg-Steenrod axioms;
in particular $H_0(\mathrm{pt}; M) = M$. -/

end HomologyWithCoefficients


-- created on 2026-10-23
