import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicTopologyI.code.Section7.Part3
open ExactSequence HomologyCrossProduct
open AlgebraicTopologyI


namespace HomologyCrossProduct

/--
[GradedBilinearMap.cross_mem_cycles](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section7.lean)
-/
@[path]
lemma GradedBilinearMap.cross_mem_cycles
  {A B C : IntChainComplex}
  {μ : GradedBilinearMap A B C}
  {p q : ℤ}
  {a : A.X p}
  {b : B.X q}
-- given
  (ha : a ∈ A.cycles p)
  (hb : b ∈ B.cycles q) :
-- imply
  (μ.cross p q) a b ∈ C.cycles (p + q) := by
-- proof
  simp only [IntChainComplex.cycles, AddMonoidHom.mem_ker] at ha hb ⊢
  rw [μ.leibniz_d p q a b, ha, hb]
  simp only [AddMonoidHom.zero_apply, map_zero, smul_zero, add_zero]

end HomologyCrossProduct

/--
[hom_cast_apply_singular](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section7.lean)
-/
@[path]
private lemma hom_cast_apply_singular_eq
  {X : Type}
  [TopologicalSpace X]
  {m n k : ℕ}
  {f : SingularChains (m + 1) X →+ SingularChains m X}
  {x : SingularChains n X}
-- given
  (h0 : m + 1 = n)
  (h1 : m = k) :
-- imply
  (h0 ▸ h1 ▸ f : SingularChains n X →+ SingularChains k X) x = cast (congrArg (SingularChains · X) h1) (f (cast (congrArg (SingularChains · X) h0.symm) x)) := by
-- proof
  apply HomologyCrossProduct.hom_cast_apply_singular X m n k h0 h1 f x

/--
[cast_singularChains_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section7.lean)
-/
@[path]
private lemma cast_singularChains_eq_zero_eq
  {X : Type}
  [TopologicalSpace X]
  {m n : ℕ}
  {x : SingularChains m X}
-- given
  (h : m = n) :
-- imply
  cast (congrArg (SingularChains · X) h) x = (0 : SingularChains n X) ↔ x = 0 := by
-- proof
  apply HomologyCrossProduct.cast_singularChains_eq_zero X h x

/--
[cast_boundaryMap_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section7.lean)
-/
@[path]
private lemma cast_boundaryMap_eq_eq
  {X : Type}
  [TopologicalSpace X]
  {m k : ℕ}
  {y : SingularChains (m + 1) X}
-- given
  (h : m = k + 1) :
-- imply
  boundaryMap k X (cast (congrArg (SingularChains · X) h) (boundaryMap m X y)) = boundaryMap k X (boundaryMap (k + 1) X (cast (congrArg (SingularChains · X) (show m + 1 = (k + 1) + 1 by omega)) y)) := by
-- proof
  apply HomologyCrossProduct.cast_boundaryMap_eq X m k h y

/--
[singularIntBoundary_comp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section7.lean)
-/
@[path]
private lemma singularIntBoundary_comp_eq
  {X : Type}
  [TopologicalSpace X]
  {n : ℤ} :
-- imply
  (singularIntBoundary X (n - 1)).comp (singularIntBoundary X n) = 0 := by
-- proof
  apply HomologyCrossProduct.singularIntBoundary_comp X n


-- created on 2026-10-23
