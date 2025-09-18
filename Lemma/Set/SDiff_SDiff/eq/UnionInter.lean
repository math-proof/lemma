import sympy.core.relational
import Lemma.Set.EqUnionSDiff__Inter
import Lemma.Set.SDiffUnion.eq.UnionSDiffS
import Lemma.Set.SubsetInter
import Lemma.Set.SDiff_SDiff.eq.Inter.of.Subset
import Lemma.Set.SubsetSDiff
import Lemma.Set.SDiffSDiff.eq.SDiff.of.Subset
import Lemma.Set.Union
open Set


@[main]
private lemma main
  {A B C : Set α} :
-- imply
  A \ (B \ C) = A ∩ B ∩ C ∪ (A \ B) := by
-- proof
  denote h_D : D = A \ B
  denote h_I : I = A ∩ B
  have h := EqUnionSDiff__Inter (s := A) (t := B)
  rw [← h_I, ← h_D] at h
  have h := h.symm
  have h : A \ (B \ C) = (D ∪ I) \ (B \ C) := by
    rw [h]
  rw [SDiffUnion.eq.UnionSDiffS] at h
  have h_Subset := SubsetInter (A := A) (B := B)
  rw [← h_I] at h_Subset
  have := SDiff_SDiff.eq.Inter.of.Subset h_Subset C
  rw [this] at h
  rw [h_D] at h
  have := SubsetSDiff (A := B) (B := C)
  have := SDiffSDiff.eq.SDiff.of.Subset this A
  rw [this] at h
  rw [h_I] at h
  rw [Union.comm] at h
  assumption


-- created on 2025-04-08
-- updated on 2025-04-30
