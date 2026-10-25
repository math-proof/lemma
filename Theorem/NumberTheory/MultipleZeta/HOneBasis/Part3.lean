/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/HOneBasis.lean -/

import Theorem.NumberTheory.MultipleZeta.WordAlgebra.Part2
import Lemma.Nat.MultipleZeta.WordAlgebra
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.DFinsupp
import Def.NumberTheory.MultipleZeta.HOneBasis.Part3
/-!
# Hoffman basis of `H^1`

Hoffman monomials indexed by all positive compositions, including the empty
index, form a rational basis of the word subalgebra `hOne` from
`MathlibExt.NumberTheory.MultipleZeta.WordAlgebra`.
-/


section

namespace MetaMathlibExt.MultipleZeta

theorem hx_span (y : ↥hOne) :
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

theorem hspan : (⊤ : Submodule ℚ ↥hOne) ≤ Submodule.span ℚ (Set.range fun idx : Index =>
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
end
