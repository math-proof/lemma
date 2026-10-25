import Mathlib
import sympy.Basic
import Def.v1.Atlas.AlgebraicTopologyI.code.CohomologyKunneth.Part2
open CategoryTheory AlgebraicTopology Limits SingularCohomology CohomologyKunneth
open scoped TensorProduct


namespace CohomologyKunneth

/--
[directSum_toModule_lof_comp_bijective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/CohomologyKunneth.lean)
-/
@[path]
lemma directSum_toModule_lof_comp_bijective
  {R' : Type}
  [CommRing R']
  {ι : Type}
  [DecidableEq ι]
  {M : ι → Type}
  [∀ i, AddCommGroup (M i)]
  [∀ i, Module R' (M i)]
  {N : ι → Type}
  [∀ i, AddCommGroup (N i)]
  [∀ i, Module R' (N i)]
-- given
  (f : ∀ i, M i →ₗ[R'] N i)
  (hf : ∀ i, Function.Bijective (f i)) :
-- imply
  Function.Bijective (DirectSum.toModule R' ι (DirectSum ι N) (fun n => (DirectSum.lof R' ι N n).comp (f n))) := by
-- proof
  have heq : DirectSum.toModule R' ι (DirectSum ι N)
    (fun n => (DirectSum.lof R' ι N n).comp (f n)) = DirectSum.lmap (R := R') f := by
    ext i m j
    simp only [DirectSum.toModule_lof, LinearMap.comp_apply]
    change ((DirectSum.lof R' ι N i) ((f i) m)) j =
      (DFinsupp.mapRange (fun i x => (f i) x) (by intro i; simp)
        ((DirectSum.lof R' ι M i) m)) j
    conv_rhs => rw [show (DirectSum.lof R' ι M i) m = (DFinsupp.single i m : Π₀ k, M k) from rfl]
    rw [DFinsupp.mapRange_single]
    rfl
  rw [heq]
  let equivs : ∀ i, M i ≃ₗ[R'] N i := fun i => LinearEquiv.ofBijective (f i) (hf i)
  have heq2 : (DirectSum.lmap (R := R') f : (DirectSum ι M) →ₗ[R'] (DirectSum ι N)) =
    (DFinsupp.mapRange.linearEquiv equivs).toLinearMap := by
    ext i m j
    change (DFinsupp.mapRange (fun i x => (f i) x) (by intro i; simp)
      ((DirectSum.lof R' ι M i) m)) j =
      (DFinsupp.mapRange (fun i x => (equivs i) x) (by intro i; simp)
      ((DirectSum.lof R' ι M i) m)) j
    congr 2
  rw [heq2]
  exact (DFinsupp.mapRange.linearEquiv equivs).bijective
/-- The tensor-product term `⨁_{p+q=m} H_p(X) ⊗_R H_q(Y)` appearing in the
homology Künneth short exact sequence is free over the PID `R` whenever
`H_*(X; R)` is finitely generated and free in every degree. -/
end CohomologyKunneth



-- created on 2026-10-23
