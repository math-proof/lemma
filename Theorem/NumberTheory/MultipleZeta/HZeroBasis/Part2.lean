/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/HZeroBasis.lean -/

import Theorem.NumberTheory.MultipleZeta.WordAlgebra.Part2
import Lemma.Nat.MultipleZeta.WordAlgebra
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Def.NumberTheory.MultipleZeta.HZeroBasis.Part2
/-!
# Multiple-zeta word bases

This file records the two substantial basis constructions left after the
proved word-subalgebra interface in
`MathlibExt.NumberTheory.MultipleZeta.WordAlgebra`.
-/


section

namespace MathlibExt.NumberTheory.MultipleZeta.WordAlgebraWanted

open MetaMathlibExt.MultipleZeta

theorem zWord_surjective :
    ∀ w ∈ wordSubmonoidHZero, ∃ idx : HZeroIndex, zWord idx.val = w := by
  intro w hw
  change IsHZeroWord w at hw
  rcases hw with rfl | ⟨u, hu⟩
  · exact ⟨⟨emptyIndex, Or.inr rfl⟩, zWord_eq_one_of_entries_eq_nil _ rfl⟩
  · have hL : FreeMonoid.toList w = [false] ++ FreeMonoid.toList u ++ [true] := by
      rw [hu]
      simp [xWord, yWord, FreeMonoid.toList_mul]
    have hL' : FreeMonoid.toList w
        = ([false] ++ FreeMonoid.toList u) ++ [true] := by
      rw [List.append_assoc]
      exact hL
    have henc : encList (decAux (FreeMonoid.toList w) 0)
        = FreeMonoid.toList w := by
      have h := encList_decAux_append_true ([false] ++ FreeMonoid.toList u) 0
      rw [← hL'] at h
      simpa using h
    have hpos : ∀ x ∈ decAux (FreeMonoid.toList w) 0, 0 < x :=
      fun x hx => decAux_pos _ 0 x hx
    obtain ⟨j, rest, hj⟩ := decAux_append_true_head (FreeMonoid.toList u) 1
    have hks : decAux (FreeMonoid.toList w) 0 = (1 + 1 + j) :: rest := by
      rw [hL']
      change decAux (FreeMonoid.toList u ++ [true]) 1 = _
      exact hj
    have hadm : Index.IsAdmissible
        ⟨(decAux (FreeMonoid.toList w) 0).sum,
          Composition.mk (decAux (FreeMonoid.toList w) 0) (fun {i} hi => hpos i hi) rfl⟩ := by
      have hlist : IsAdmissible (decAux (FreeMonoid.toList w) 0) := by
        rw [hks]
        refine ⟨by omega, fun x hx => ?_⟩
        exact hpos x (by rw [hks]; exact List.mem_cons_of_mem _ hx)
      exact (Index.isAdmissible_iff _).mpr hlist
    refine ⟨⟨⟨(decAux (FreeMonoid.toList w) 0).sum,
      Composition.mk (decAux (FreeMonoid.toList w) 0) (fun {i} hi => hpos i hi) rfl⟩,
        Or.inl hadm⟩, ?_⟩
    apply FreeMonoid.toList.injective
    rw [toList_zWord]
    exact henc

theorem hZero_span_eq :
    Submodule.span ℚ (Set.range (fun idx : HZeroIndex => zMonomial idx.val))
      = hZero.toSubmodule := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨idx, rfl⟩
    exact (Subalgebra.mem_toSubmodule hZero).mpr
      (zMonomial_mem_hZero idx.val idx.property)
  · intro x hx
    have hxH : x ∈ hZero := (Subalgebra.mem_toSubmodule hZero).mp hx
    have hsupp : ∀ w ∈ (FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := ℚ) (X := Bool)
        x).coeff.support, w ∈ wordSubmonoidHZero :=
      (mem_hZero_iff_support_subset x).mp hxH
    have hback : x = (FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := ℚ) (X := Bool)).symm
        (((FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := ℚ) (X := Bool))
          x).coeff.sum MonoidAlgebra.single) := by
      rw [MonoidAlgebra.sum_coeff_single]
      exact (AlgEquiv.symm_apply_apply _ x).symm
    rw [hback]
    change (FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := ℚ) (X := Bool)).symm
        (∑ w ∈ ((FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := ℚ) (X := Bool))
          x).coeff.support, MonoidAlgebra.single w
            (((FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := ℚ) (X := Bool)) x).coeff w))
        ∈ Submodule.span ℚ (Set.range (fun idx : HZeroIndex => zMonomial idx.val))
    rw [map_sum]
    refine Submodule.sum_mem _ (fun w hw => ?_)
    have hwS : w ∈ wordSubmonoidHZero := hsupp w hw
    obtain ⟨idx, hidx⟩ := zWord_surjective w hwS
    have hsmul : MonoidAlgebra.single w
          (((FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := ℚ) (X := Bool)) x).coeff w)
        = (((FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := ℚ) (X := Bool)) x).coeff w)
          • MonoidAlgebra.single (zWord idx.val) 1 := by
      rw [← hidx]
      simp
    have hback2 : (FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := ℚ) (X := Bool)).symm
          (MonoidAlgebra.single w
            (((FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := ℚ) (X := Bool)) x).coeff w))
        = (((FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := ℚ) (X := Bool)) x).coeff w)
          • zMonomial idx.val := by
      rw [hsmul, map_smul]
      simp only [zMonomial]
    rw [hback2]
    exact Submodule.smul_mem _ _
      (Submodule.subset_span ⟨idx, rfl⟩)

end MathlibExt.NumberTheory.MultipleZeta.WordAlgebraWanted
end
