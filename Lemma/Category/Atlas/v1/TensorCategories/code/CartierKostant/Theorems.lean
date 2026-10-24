import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.TensorCategories.code.CartierKostant.Axioms
import Lemma.Category.Atlas.v1.TensorCategories.code.CartierKostant.Axioms
open Coalgebra HopfAlgebra
open scoped TensorProduct


/--
[HopfAlgebra.milnorMoore_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CartierKostant/Theorems.lean)
-/
@[path]
lemma HopfAlgebra.milnorMoore_injective
  {k : Type u}
  {H : Type v}
  [Field k]
  [IsAlgClosed k]
  [CharZero k]
  [Ring H]
  [HopfAlgebra k H]
  [Coalgebra.IsCocommutative k H]
-- given
  (hconn : HopfAlgebra.grouplikeElements (R := k) (H := H) = {1}) :
-- imply
  Function.Injective (HopfAlgebra.canonicalMapUEA (R := k) (H := H)) := by
-- proof
  obtain ⟨F, hMono, hExhaust, _hCompat, hBase, hGraded⟩ :=
    HopfAlgebra.coradicalFiltration_compatible_injective k H hconn
  have hKerFilt : ∀ n x, x ∈ F n →
    (HopfAlgebra.canonicalMapUEA (R := k) (H := H)) x = 0 → x = 0 := by
    intro n
    induction n with
    | zero => exact hBase
    | succ n ih =>
      intro x hxF hψx
      exact ih x (hGraded n x hxF hψx) hψx
  intro a b hab
  rw [← sub_eq_zero]
  have hψ_diff : (HopfAlgebra.canonicalMapUEA (R := k) (H := H)) (a - b) = 0 := by
    rw [map_sub, sub_eq_zero]; exact hab
  have hMem : a - b ∈ (⨆ n, F n) := by rw [hExhaust]; exact Submodule.mem_top
  obtain ⟨n, hn⟩ := (Submodule.mem_iSup_of_directed F (hMono.directed_le)).mp hMem
  exact hKerFilt n _ hn hψ_diff

/--
[HopfAlgebra.cartierKostant](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CartierKostant/Theorems.lean)
-/
@[path]
lemma HopfAlgebra.cartierKostant
  {k : Type u}
  {H : Type v}
  [Field k]
  [IsAlgClosed k]
  [CharZero k]
  [Ring H]
  [HopfAlgebra k H]
  [Coalgebra.IsCocommutative k H] :
-- imply
  Algebra.adjoin k (HopfAlgebra.grouplikeElements (R := k) (H := H) ∪ (HopfAlgebra.primitiveElements (R := k) (H := H) : Set H)) = ⊤ := by
-- proof
  have hDecomp := HopfAlgebra.pointedCoalgebraDecomposition k H
  have hRange : (Set.range (HopfAlgebra.canonicalMapUEA (R := k) (H := H))) ⊆
    ↑(Algebra.adjoin k (HopfAlgebra.primitiveElements (R := k) (H := H) : Set H)) := by
    intro x hx
    rw [Set.mem_range] at hx
    obtain ⟨y, rfl⟩ := hx
    exact HopfAlgebra.canonicalMapUEA_range_le_adjoin ⟨y, rfl⟩
  rw [eq_top_iff, ← hDecomp]
  apply Algebra.adjoin_le
  intro x hx
  obtain hG | hψ := hx
  · exact Algebra.adjoin_mono Set.subset_union_left (Algebra.subset_adjoin hG)
  · exact Algebra.adjoin_mono Set.subset_union_right (hRange hψ)

/--
[thm_1_33_1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CartierKostant/Theorems.lean)
-/
@[path]
lemma thm_1_33_1
  {k : Type u}
  {H : Type u}
  [Field k]
  [IsAlgClosed k]
  [CharZero k]
  [Ring H]
  [HopfAlgebra k H]
  [Coalgebra.IsCocommutative k H] :
-- imply
  let G := HopfAlgebra.GrouplikeGroup k H let 𝔤 := HopfAlgebra.primitiveLieSubalgebra (R := k) (H := H) let act := HopfAlgebra.grouplikeConjugationAction k H Nonempty (@AlgEquiv k (@SmashProductAlgebra k G 𝔤 _ _ _ _ act) H _ (@SmashProductAlgebra.instRing k G 𝔤 _ _ _ _ act).toSemiring (inferInstance : Semiring H) (@SmashProductAlgebra.instAlgebra k G 𝔤 _ _ _ _ act) (inferInstance : Algebra k H)) :=
-- proof
  HopfAlgebra.cartierKostant_iso k H

/--
[Theorem_1_33_1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CartierKostant/Theorems.lean)
-/
@[path]
lemma Theorem_1_33_1
  {k : Type u}
  {H : Type u}
  [Field k]
  [IsAlgClosed k]
  [CharZero k]
  [Ring H]
  [HopfAlgebra k H]
  [Coalgebra.IsCocommutative k H] :
-- imply
  let G := HopfAlgebra.GrouplikeGroup k H let 𝔤 := HopfAlgebra.primitiveLieSubalgebra (R := k) (H := H) let act := HopfAlgebra.grouplikeConjugationAction k H Nonempty (@AlgEquiv k (@SmashProductAlgebra k G 𝔤 _ _ _ _ act) H _ (@SmashProductAlgebra.instRing k G 𝔤 _ _ _ _ act).toSemiring (inferInstance : Semiring H) (@SmashProductAlgebra.instAlgebra k G 𝔤 _ _ _ _ act) (inferInstance : Algebra k H)) :=
-- proof
  thm_1_33_1 k H

/--
[cartierKostant](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CartierKostant/Theorems.lean)
-/
@[path]
lemma cartierKostant
  {k : Type u}
  {H : Type v}
  [Field k]
  [IsAlgClosed k]
  [CharZero k]
  [Ring H]
  [HopfAlgebra k H]
  [Coalgebra.IsCocommutative k H] :
-- imply
  Algebra.adjoin k (HopfAlgebra.grouplikeElements (R := k) (H := H) ∪ (HopfAlgebra.primitiveElements (R := k) (H := H) : Set H)) = ⊤ :=
-- proof
  HopfAlgebra.cartierKostant k H

/--
[HopfAlgebra.milnorMoore_primitives_generate](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CartierKostant/Theorems.lean)
-/
@[path]
lemma HopfAlgebra.milnorMoore_primitives_generate
  {k : Type u}
  {H : Type v}
  [Field k]
  [IsAlgClosed k]
  [CharZero k]
  [Ring H]
  [HopfAlgebra k H]
  [Coalgebra.IsCocommutative k H]
-- given
  (hconn : HopfAlgebra.grouplikeElements (R := k) (H := H) = {1}) :
-- imply
  Algebra.adjoin k ((HopfAlgebra.primitiveElements (R := k) (H := H) : Set H)) = ⊤ := by
-- proof
  have hCK := HopfAlgebra.cartierKostant k H
  rw [hconn] at hCK
  rw [eq_top_iff, ← hCK]
  apply Algebra.adjoin_le
  intro x hx
  cases hx with
  | inl h => rw [Set.mem_singleton_iff.mp h]; exact Subalgebra.one_mem _
  | inr h => exact Algebra.subset_adjoin h

/--
[HopfAlgebra.milnorMoore](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CartierKostant/Theorems.lean)
-/
@[path]
lemma HopfAlgebra.milnorMoore
  {k : Type u}
  {H : Type v}
  [Field k]
  [IsAlgClosed k]
  [CharZero k]
  [Ring H]
  [HopfAlgebra k H]
  [Coalgebra.IsCocommutative k H]
-- given
  (hconn : HopfAlgebra.grouplikeElements (R := k) (H := H) = {1}) :
-- imply
  Function.Bijective (HopfAlgebra.canonicalMapUEA (R := k) (H := H)) :=
-- proof
  ⟨HopfAlgebra.milnorMoore_injective k H hconn,
    HopfAlgebra.surjective_of_primitives_generate
      (HopfAlgebra.milnorMoore_primitives_generate k H hconn)⟩

/--
[HopfAlgebra.pointedDecomposition](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CartierKostant/Theorems.lean)
-/
@[path]
lemma HopfAlgebra.pointedDecomposition
  {k : Type u}
  {H : Type v}
  [Field k]
  [IsAlgClosed k]
  [CharZero k]
  [Ring H]
  [HopfAlgebra k H]
  [Coalgebra.IsCocommutative k H] :
-- imply
  Algebra.adjoin k (HopfAlgebra.grouplikeElements (R := k) (H := H) ∪ Set.range (HopfAlgebra.canonicalMapUEA (R := k) (H := H))) = ⊤ :=
-- proof
  HopfAlgebra.pointedCoalgebraDecomposition k H

/--
[HopfAlgebra.commHopfAlgebra_isGeometricallyReduced](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CartierKostant/Theorems.lean)
-/
@[path]
lemma HopfAlgebra.commHopfAlgebra_isGeometricallyReduced
  {k : Type u}
  {H : Type v}
  [Field k]
  [CharZero k]
  [CommRing H]
  [HopfAlgebra k H] :
-- imply
  Algebra.IsGeometricallyReduced k H :=
-- proof
  Algebra.IsGeometricallyReduced.of_forall_fg fun B hB =>
    HopfAlgebra.commHopfAlgebra_fg_subalgebra_isGeometricallyReduced k H B hB

/--
[HopfAlgebra.commHopfAlgebra_isReduced](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CartierKostant/Theorems.lean)
-/
@[path]
lemma HopfAlgebra.commHopfAlgebra_isReduced
  {k : Type u}
  {H : Type v}
  [Field k]
  [CharZero k]
  [CommRing H]
  [HopfAlgebra k H] :
-- imply
  IsReduced H := by
-- proof
  haveI := HopfAlgebra.commHopfAlgebra_isGeometricallyReduced k H
  exact Algebra.isReduced_of_isGeometricallyReduced k

/--
[Corollary_1_33_4](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CartierKostant/Theorems.lean)
-/
@[path]
lemma Corollary_1_33_4
  {k : Type u}
  {H : Type v}
  [Field k]
  [CharZero k]
  [CommRing H]
  [HopfAlgebra k H] :
-- imply
  IsReduced H :=
-- proof
  HopfAlgebra.commHopfAlgebra_isReduced k H
section Consequences
variable {k : Type u} {H : Type v}

/--
[HopfAlgebra.milnorMoore_generation](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CartierKostant/Theorems.lean)
-/
@[path]
lemma HopfAlgebra.milnorMoore_generation
  {k : Type u}
  {H : Type v}
  [Field k]
  [IsAlgClosed k]
  [CharZero k]
  [Ring H]
  [HopfAlgebra k H]
  [Coalgebra.IsCocommutative k H]
-- given
  (hconn : HopfAlgebra.grouplikeElements (R := k) (H := H) = {1}) :
-- imply
  Algebra.adjoin k ((HopfAlgebra.primitiveElements (R := k) (H := H) : Set H)) = ⊤ :=
-- proof
  HopfAlgebra.surjective_canonicalMapUEA_adjoin_top
    (HopfAlgebra.milnorMoore k H hconn).2

/--
[HopfAlgebra.IsPrimitive.isSkewPrimitive_one_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CartierKostant/Theorems.lean)
-/
@[path]
lemma HopfAlgebra.IsPrimitive.isSkewPrimitive_one_one
  {k : Type u}
  {H : Type v}
  [CommRing k]
  [Ring H]
  [HopfAlgebra k H]
  {x : H}
-- given
  (hx : HopfAlgebra.IsPrimitive (R := k) x) :
-- imply
  IsSkewPrimitive (R := k) (1 : H) (1 : H) x := by
-- proof
  show comul (R := k) x = x ⊗ₜ 1 + 1 ⊗ₜ x
  exact hx

/--
[HopfAlgebra.IsPrimitive.mem_coradicalFiltration_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CartierKostant/Theorems.lean)
-/
@[path]
lemma HopfAlgebra.IsPrimitive.mem_coradicalFiltration_one
  {k : Type u}
  {H : Type v}
  [CommRing k]
  [Ring H]
  [HopfAlgebra k H]
  {x : H}
-- given
  (hx : HopfAlgebra.IsPrimitive (R := k) x)
  (h0 : (1 : H) ∈ coradical (R := k) (C := H)) :
-- imply
  x ∈ coradicalFiltration (R := k) (C := H) 1 :=
-- proof
  skewPrimitive_mem_coradicalFiltration_one 1 1 x h1 h1 hx.isSkewPrimitive_one_one

/--
[HopfAlgebra.comul_symmetric](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CartierKostant/Theorems.lean)
-/
@[path]
lemma HopfAlgebra.comul_symmetric
  {k : Type u}
  {H : Type v}
  [CommRing k]
  [Ring H]
  [HopfAlgebra k H]
  [Coalgebra.IsCocommutative k H]
  {x : H} :
-- imply
  (TensorProduct.comm k H H) (comul (R := k) x) = comul (R := k) x :=
-- proof
  cocommutative_comul_apply k H x

/--
[HopfAlgebra.IsGrouplikeHopf.toIsGrouplike](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CartierKostant/Theorems.lean)
-/
@[path]
lemma HopfAlgebra.IsGrouplikeHopf.toIsGrouplike
  {k : Type u}
  {H : Type v}
  [CommRing k]
  [Ring H]
  [HopfAlgebra k H]
  {g : H}
-- given
  (hg : HopfAlgebra.IsGrouplikeHopf (R := k) g) :
-- imply
  IsGrouplike (R := k) g :=
-- proof
  hg

/--
[HopfAlgebra.IsGrouplikeHopf.antipode_isUnit](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CartierKostant/Theorems.lean)
-/
@[path]
lemma HopfAlgebra.IsGrouplikeHopf.antipode_isUnit
  {k : Type u}
  {H : Type v}
  [CommRing k]
  [Ring H]
  [HopfAlgebra k H]
  {g : H}
-- given
  (hg : HopfAlgebra.IsGrouplikeHopf (R := k) g) :
-- imply
  IsUnit (antipode k g) :=
-- proof
  ⟨⟨antipode k g, g, hg.antipode_mul, hg.mul_antipode⟩, rfl⟩

/--
[HopfAlgebra.commHopfAlgebra_no_nilpotents](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CartierKostant/Theorems.lean)
-/
@[path]
lemma HopfAlgebra.commHopfAlgebra_no_nilpotents
  {k : Type u}
  {H : Type v}
  [Field k]
  [CharZero k]
  [CommRing H]
  [HopfAlgebra k H]
  {x : H}
-- given
  (hx : IsNilpotent x) :
-- imply
  x = 0 := by
-- proof
  haveI := HopfAlgebra.commHopfAlgebra_isReduced k H
  exact hx.eq_zero
end Consequences


-- created on 2026-10-23
