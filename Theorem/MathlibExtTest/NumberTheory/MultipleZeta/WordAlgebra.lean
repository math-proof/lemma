/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/MultipleZeta/WordAlgebra.lean -/


import Theorem.NumberTheory.MultipleZeta.WordAlgebra.Part2
import Lemma.Nat.MultipleZeta.WordAlgebra


namespace MetaMathlibExt.MultipleZeta

/-- Empty `zWord` is the scalar word. -/
example (idx : Index) (h : idx.entries = []) : zWord idx = 1 := by
  exact zWord_eq_one_of_entries_eq_nil idx h

/-- One-block word in source order. -/
example (k : PNat) : zWordPNat [k] = hoffmanBlock k := by
  simp [zWordPNat]

/-- Multi-block word concatenates blocks in source order. -/
example (k1 k2 : PNat) :
    zWordPNat [k1, k2] = hoffmanBlock k1 * hoffmanBlock k2 := by
  simp [zWordPNat, List.prod_cons]

/-- Admissible word lies in `H^0`: `z_2 = x*y`. -/
example : hoffmanBlock ⟨2, by decide⟩ ∈ wordSubmonoidHZero :=
  hoffmanBlock_mem_hZero_of_two_le ⟨2, by decide⟩ (by decide)

/-- Non-admissible boundary `z_1 = y` lies in `H^1` but not in `H^0`. -/
example : yWord ∈ wordSubmonoidHOne := by
  change IsHOneWord yWord
  exact Or.inr ⟨1, by simp [yWord]⟩

example : yWord ∉ wordSubmonoidHZero := by
  intro h
  change IsHZeroWord yWord at h
  rcases h with h1 | ⟨u, hu⟩
  · have h2 := congrArg FreeMonoid.toList h1
    simp [yWord] at h2
  · have h2 := congrArg FreeMonoid.toList hu
    simp [xWord, yWord] at h2

/-- Representative `zMonomial` equality via the free-algebra equivalence. -/
example (idx : Index) :
    (FreeAlgebra.equivMonoidAlgebraFreeMonoid :
      FreeAlgebra ℚ Bool ≃ₐ[ℚ] MonoidAlgebra ℚ (FreeMonoid Bool))
      (zMonomial idx) = MonoidAlgebra.single (zWord idx) 1 := by
  simp [zMonomial]

example : zMonomial (⟨0, ⟨[], by simp, by simp⟩⟩ : Index) ∈ hOne :=
  zMonomial_mem_hOne _

example (idx : Index) (h : IsHZeroIndex idx) : zMonomial idx ∈ hZero :=
  zMonomial_mem_hZero idx h

example (idx : Index) :
    ∀ w ∈ (FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := ℚ)
      (zMonomial idx)).coeff.support, w ∈ wordSubmonoidHOne :=
  (mem_hOne_iff_support_subset _).mp (zMonomial_mem_hOne idx)

example : FreeAlgebra.ι ℚ (false : Bool) ∉ hOne :=
  generatorX_not_mem_hOne

/-- Proved inclusion `H^0 ≤ H^1`. -/
example : hZero ≤ hOne := hZero_le_hOne

/-- Every Hoffman word belongs to `H^1`. -/
example (idx : Index) : zWord idx ∈ wordSubmonoidHOne :=
  zWord_mem_hOne idx

/-- Every empty or admissible Hoffman word belongs to `H^0`. -/
example (idx : Index) (h : IsHZeroIndex idx) :
    zWord idx ∈ wordSubmonoidHZero :=
  zWord_mem_hZero idx h

end MetaMathlibExt.MultipleZeta
