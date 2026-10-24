/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/HZeroBasis.lean -/

import sympy.atlas.NumberTheory.MultipleZeta.WordAlgebra
import Lemma.Nat.MultipleZeta.WordAlgebra
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-!
# Multiple-zeta word bases

This file records the two substantial basis constructions left after the
proved word-subalgebra interface in
`MathlibExt.NumberTheory.MultipleZeta.WordAlgebra`.
-/

section
namespace MathlibExt.NumberTheory.MultipleZeta.WordAlgebraWanted

open MetaMathlibExt.MultipleZeta

private def encBlock (n : Nat) : List Bool :=
  List.replicate (n - 1) false ++ [true]

private def encList (l : List Nat) : List Bool :=
  (l.map encBlock).flatten

private def decAux : List Bool → Nat → List Nat
  | [], n => if n = 0 then [] else [n + 1]
  | false :: t, n => decAux t (n + 1)
  | true :: t, n => (n + 1) :: decAux t 0

private theorem decAux_pos (L : List Bool) :
    ∀ (n x : Nat), x ∈ decAux L n → 0 < x := by
  induction L with
  | nil =>
    intro n x hx
    simp only [decAux] at hx
    by_cases hn : n = 0
    · simp [hn] at hx
    · simp [hn] at hx
      omega
  | cons b t ih =>
    intro n x hx
    cases b with
    | false =>
      simp only [decAux] at hx
      exact ih (n + 1) x hx
    | true =>
      simp only [decAux, List.mem_cons] at hx
      rcases hx with h | hx
      · omega
      · exact ih 0 x hx

private theorem rep_append_cons (n : Nat) (X : List Bool) :
    List.replicate n false ++ (false :: X)
      = false :: (List.replicate n false ++ X) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, List.cons_append, List.cons_append, ih]

private theorem encList_decAux_append_true (L' : List Bool) (n : Nat) :
    encList (decAux (L' ++ [true]) n) = List.replicate n false ++ (L' ++ [true]) := by
  induction L' generalizing n with
  | nil =>
    simp only [List.nil_append]
    have e1 : decAux ([true] : List Bool) n = [n + 1] := rfl
    rw [e1]
    have e2 : encList [n + 1] = encBlock (n + 1) := by simp [encList]
    rw [e2]
    simp [encBlock]
  | cons b t ih =>
    cases b with
    | false =>
      have e1 : ((false :: t) ++ [true]) = false :: (t ++ [true]) := rfl
      rw [e1]
      have e2 : decAux (false :: (t ++ [true])) n = decAux (t ++ [true]) (n + 1) := rfl
      rw [e2, ih, List.replicate_succ, List.cons_append, rep_append_cons]
    | true =>
      have e1 : ((true :: t) ++ [true]) = true :: (t ++ [true]) := rfl
      rw [e1]
      have e2 : decAux (true :: (t ++ [true])) n
          = (n + 1) :: decAux (t ++ [true]) 0 := rfl
      rw [e2]
      have e3 : encList ((n + 1) :: decAux (t ++ [true]) 0)
          = encBlock (n + 1) ++ encList (decAux (t ++ [true]) 0) := rfl
      rw [e3, ih]
      simp [encBlock, List.append_assoc]

private theorem decAux_append_true_head (M' : List Bool) (n : Nat) :
    ∃ j rest, decAux (M' ++ [true]) n = (n + 1 + j) :: rest := by
  induction M' generalizing n with
  | nil =>
    exact ⟨0, decAux [] 0, rfl⟩
  | cons b t ih =>
    cases b with
    | false =>
      have e1 : ((false :: t) ++ [true]) = false :: (t ++ [true]) := rfl
      rw [e1]
      have e2 : decAux (false :: (t ++ [true])) n = decAux (t ++ [true]) (n + 1) := rfl
      rw [e2]
      obtain ⟨j, rest, hj⟩ := ih (n + 1)
      refine ⟨j + 1, rest, ?_⟩
      rw [hj]
      congr 1
      omega
    | true =>
      exact ⟨0, decAux (t ++ [true]) 0, rfl⟩

private theorem toList_zWordPNat (l : List PNat) :
    FreeMonoid.toList (zWordPNat l) = encList (l.map PNat.val) := by
  induction l with
  | nil => simp [zWordPNat, encList]
  | cons k ks ih =>
    have e : zWordPNat (k :: ks) = hoffmanBlock k * zWordPNat ks := rfl
    rw [e, FreeMonoid.toList_mul, toList_hoffmanBlock, ih]
    simp [encList, encBlock]

private theorem toList_zWord (idx : Index) :
    FreeMonoid.toList (zWord idx) = encList idx.entries := by
  have e : zWord idx = zWordPNat idx.pnatEntries := rfl
  rw [e, toList_zWordPNat, pnatEntries_val]

private theorem zWord_injective : Function.Injective zWord := by
  intro a b hab
  have h := congrArg FreeMonoid.toList hab
  rw [toList_zWord, toList_zWord] at h
  have he := encList_inj a.entries (entries_pos a) b.entries (entries_pos b) h
  exact entries_injective he

private def emptyIndex : Index :=
  ⟨0, Composition.mk [] (by simp) rfl⟩

private theorem zWord_surjective :
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

private theorem hZero_span_eq :
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

private def spanEquivHZero :
    ↥(Submodule.span ℚ (Set.range (fun idx : HZeroIndex => zMonomial idx.val))) ≃ₗ[ℚ]
      ↥hZero where
  toFun x := ⟨x.val, (Subalgebra.mem_toSubmodule hZero).mp (hZero_span_eq ▸ x.property)⟩
  invFun x := ⟨x.val, hZero_span_eq.symm ▸ (Subalgebra.mem_toSubmodule hZero).mpr x.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl
end MathlibExt.NumberTheory.MultipleZeta.WordAlgebraWanted
