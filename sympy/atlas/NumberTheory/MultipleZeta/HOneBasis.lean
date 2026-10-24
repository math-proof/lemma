/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/HOneBasis.lean -/

import sympy.atlas.NumberTheory.MultipleZeta.WordAlgebra
import Lemma.Nat.MultipleZeta.WordAlgebra
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.DFinsupp

/-!
# Hoffman basis of `H^1`

Hoffman monomials indexed by all positive compositions, including the empty
index, form a rational basis of the word subalgebra `hOne` from
`MathlibExt.NumberTheory.MultipleZeta.WordAlgebra`.
-/

section
namespace MetaMathlibExt.MultipleZeta

/-- Increment the leading block size; auxiliary for `decodeBlocks`. -/
private def bump : List Nat → List Nat
  | [] => []
  | k :: ks => (k + 1) :: ks

/-- Encode a list of block sizes as a word over `{x, y}`. -/
private def encodeNatBlocks : List Nat → List Bool
  | [] => []
  | k :: ks => List.replicate (k - 1) false ++ [true] ++ encodeNatBlocks ks

/-- Decode a word over `{x, y}` into block sizes, dropping a trailing
open `x`-run (which never occurs for `H^1` words). -/
private def decodeBlocks : List Bool → List Nat
  | [] => []
  | true :: rest => 1 :: decodeBlocks rest
  | false :: rest => bump (decodeBlocks rest)

private theorem decodeBlocks_pos (l : List Bool) : ∀ x ∈ decodeBlocks l, 0 < x := by
  induction l with
  | nil =>
    intro x hx
    simp [decodeBlocks] at hx
  | cons b rest ih =>
    cases b with
    | true =>
      intro x hx
      simp only [decodeBlocks, List.mem_cons] at hx
      rcases hx with rfl | hx
      · omega
      · exact ih x hx
    | false =>
      intro x hx
      simp only [decodeBlocks] at hx
      cases h : decodeBlocks rest with
      | nil => rw [h] at hx; simp [bump] at hx
      | cons k ks =>
        rw [h] at hx
        simp only [bump, List.mem_cons] at hx
        rcases hx with rfl | hx
        · omega
        · apply ih
          rw [h]
          exact List.mem_cons_of_mem k hx

private theorem encodeNatBlocks_decodeBlocks (l : List Bool)
    (h : l = [] ∨ l.getLast? = some true) :
    encodeNatBlocks (decodeBlocks l) = l := by
  induction l with
  | nil => simp [decodeBlocks, encodeNatBlocks]
  | cons b rest ih =>
    cases b with
    | true =>
      have hr : rest = [] ∨ rest.getLast? = some true := by
        cases rest with
        | nil => exact Or.inl rfl
        | cons c cs =>
          exact Or.inr (by
            have hlast := Or.resolve_left h (by simp)
            rwa [List.getLast?_cons_cons] at hlast)
      have ihr := ih hr
      simp [decodeBlocks, encodeNatBlocks, ihr]
    | false =>
      cases rest with
      | nil => simp at h
      | cons c cs =>
        have hlast : (c :: cs).getLast? = some true := by
          have hlast := Or.resolve_left h (by simp)
          rwa [List.getLast?_cons_cons] at hlast
        have hr : (c :: cs) = [] ∨ (c :: cs).getLast? = some true :=
          Or.inr hlast
        have ihr := ih hr
        have hmem : true ∈ (c :: cs) := true_mem_of_getLast?_eq_true _ hlast
        have hne : decodeBlocks (c :: cs) ≠ [] :=
          decodeBlocks_ne_nil_of_mem_true _ hmem
        cases hd : decodeBlocks (c :: cs) with
        | nil => exact absurd hd hne
        | cons k ks =>
          have hdec : decodeBlocks (false :: c :: cs) = (k + 1) :: ks := by
            simp [decodeBlocks, hd, bump]
          rw [hdec]
          have henc : encodeNatBlocks ((k + 1) :: ks) =
              List.replicate k false ++ [true] ++ encodeNatBlocks ks := by
            simp [encodeNatBlocks]
          rw [henc]
          have hrest : (c :: cs) = encodeNatBlocks (k :: ks) := by
            rw [← hd]; exact ihr.symm
          have hkpos : 0 < k := decodeBlocks_pos (c :: cs) k (by rw [hd]; simp)
          have hrep : List.replicate k false =
              false :: List.replicate (k - 1) false := by
            cases k with
            | zero => simp at hkpos
            | succ n => simp [List.replicate_succ]
          rw [hrep]
          simp [hrest, encodeNatBlocks]

/-- Index decoding an `H^1` word by splitting after each `y`. -/
private def indexOfHOneWord (w : FreeMonoid Bool) : Index :=
  ⟨(decodeBlocks (FreeMonoid.toList w)).sum,
    ⟨decodeBlocks (FreeMonoid.toList w),
     fun {i} hi => decodeBlocks_pos (FreeMonoid.toList w) i hi, rfl⟩⟩

private theorem zWord_indexOfHOneWord (w : FreeMonoid Bool)
    (h : w ∈ wordSubmonoidHOne) : zWord (indexOfHOneWord w) = w := by
  apply FreeMonoid.toList.injective
  have h1 : FreeMonoid.toList (zWord (indexOfHOneWord w)) =
      encodeNatBlocks ((indexOfHOneWord w).entries) := by
    have h2 := toList_zWordPNat (indexOfHOneWord w).pnatEntries
    rw [pnatEntries_val] at h2
    exact h2
  rw [h1]
  change encodeNatBlocks (decodeBlocks (FreeMonoid.toList w)) = FreeMonoid.toList w
  exact encodeNatBlocks_decodeBlocks _ ((mem_HOne_iff_toList w).mp h)

/-- Linear-equiv version of the free-algebra identification. -/
private noncomputable def freeAlgEquiv :
    FreeAlgebra ℚ Bool ≃ₗ[ℚ] MonoidAlgebra ℚ (FreeMonoid Bool) :=
  (FreeAlgebra.equivMonoidAlgebraFreeMonoid :
    FreeAlgebra ℚ Bool ≃ₐ[ℚ] MonoidAlgebra ℚ (FreeMonoid Bool)).toLinearEquiv

private theorem hx_span (y : ↥hOne) :
    (↑y : FreeAlgebra ℚ Bool) ∈
      Submodule.span ℚ (Set.range fun idx : Index => zMonomial idx) := by
  set Fx : MonoidAlgebra ℚ (FreeMonoid Bool) :=
    freeAlgEquiv (↑y : FreeAlgebra ℚ Bool) with hFx
  have hsupp : ∀ w ∈ Fx.coeff.support, w ∈ wordSubmonoidHOne := by
    have h := (mem_hOne_iff_support_subset (↑y : FreeAlgebra ℚ Bool)).mp y.property
    exact h
  have hFxmem : Fx ∈ Submodule.span ℚ
      (Set.range fun idx : Index => MonoidAlgebra.single (zWord idx) (1 : ℚ)) := by
    rw [hdecomp Fx]
    apply Submodule.sum_mem
    intro w hw
    have hwm : w ∈ wordSubmonoidHOne := hsupp w hw
    have hzw : zWord (indexOfHOneWord w) = w := zWord_indexOfHOneWord w hwm
    have hmem : MonoidAlgebra.single w (1 : ℚ) ∈
        Set.range fun idx : Index => MonoidAlgebra.single (zWord idx) (1 : ℚ) :=
      ⟨indexOfHOneWord w,
        congrArg (fun u => MonoidAlgebra.single u (1 : ℚ)) hzw⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)
  have hfun : (⇑freeAlgEquiv.symm.toLinearMap ∘
        fun idx : Index => MonoidAlgebra.single (zWord idx) (1 : ℚ)) =
        (fun idx : Index => zMonomial idx) := rfl
  have himg : (⇑freeAlgEquiv.symm.toLinearMap) ''
        (Set.range fun idx : Index => MonoidAlgebra.single (zWord idx) (1 : ℚ))
      = Set.range fun idx : Index => zMonomial idx := by
    rw [← Set.range_comp, hfun]
  have hmap : Submodule.map freeAlgEquiv.symm.toLinearMap (Submodule.span ℚ
      (Set.range fun idx : Index => MonoidAlgebra.single (zWord idx) (1 : ℚ)))
      = Submodule.span ℚ (Set.range fun idx : Index => zMonomial idx) := by
    rw [Submodule.map_span, himg]
  have hmem2 : freeAlgEquiv.symm Fx ∈ Submodule.span ℚ
      (Set.range fun idx : Index => zMonomial idx) := by
    rw [← hmap]
    exact Submodule.mem_map.mpr ⟨Fx, hFxmem, rfl⟩
  have hEL : freeAlgEquiv.symm Fx = (↑y : FreeAlgebra ℚ Bool) := by
    rw [hFx]
    exact freeAlgEquiv.symm_apply_apply _
  rwa [hEL] at hmem2

private theorem hspan : (⊤ : Submodule ℚ ↥hOne) ≤ Submodule.span ℚ (Set.range fun idx : Index =>
    (⟨zMonomial idx, zMonomial_mem_hOne idx⟩ : ↥hOne)) := by
  intro y _
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp (hx_span y)
  refine Finsupp.mem_span_range_iff_exists_finsupp.mpr ⟨c, ?_⟩
  apply Subtype.ext
  have hcoe : (Submodule.subtype hOne.toSubmodule)
        (c.sum fun i a => a • (⟨zMonomial i, zMonomial_mem_hOne i⟩ : ↥hOne))
      = c.sum (fun i a => a • zMonomial i) := by
    change (Submodule.subtype hOne.toSubmodule (∑ i ∈ c.support, (c i) •
        (⟨zMonomial i, zMonomial_mem_hOne i⟩ : ↥hOne)))
        = (∑ i ∈ c.support, (c i) • zMonomial i)
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hsub : (Submodule.subtype hOne.toSubmodule)
        ((⟨zMonomial i, zMonomial_mem_hOne i⟩ : ↥hOne)) = zMonomial i := rfl
    rw [map_smul, hsub]
  change (Submodule.subtype hOne.toSubmodule) (c.sum fun i a => a •
      (⟨zMonomial i, zMonomial_mem_hOne i⟩ : ↥hOne)) = ↑y
  rw [hcoe, hc]

end MetaMathlibExt.MultipleZeta
end

section
namespace MathlibExt.NumberTheory.MultipleZeta.WordAlgebraWanted

open MetaMathlibExt.MultipleZeta

/-- Hoffman monomials, including the empty word, form a rational basis of `H^1`.

Source: M. E. Hoffman, *The Algebra of Multiple Harmonic Series*, J. Algebra 194
(1997), 477–495, DOI 10.1006/jabr.1997.7127.

Proves `Wanted` entry `hOne_basis`.
-/
theorem hOne_basis :
    ∃ b : Module.Basis Index ℚ ↥hOne,
      ∀ idx : Index, (↑(b idx) : FreeAlgebra ℚ Bool) = zMonomial idx := by
  refine ⟨Module.Basis.mk hliSub hspan, fun idx => ?_⟩
  simp [Module.Basis.mk_apply]

end MathlibExt.NumberTheory.MultipleZeta.WordAlgebraWanted
