import Mathlib
import sympy.Basic
import Theorem.NumberTheory.MultipleZeta.HOneBasis.Part3
open `x`-run (which never occurs for `H^1` words). -/
open MetaMathlibExt.MultipleZeta
open MathlibExt.NumberTheory.MultipleZeta.WordAlgebraWanted


namespace MetaMathlibExt.MultipleZeta

/--
[bump_ne_nil_of_ne_nil](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/HOneBasis.lean)
-/
@[path]
private lemma bump_ne_nil_of_ne_nil (l : List Nat) (h : l ≠ []) : bump l ≠ [] := by
  cases l with
  | nil => simp at h
  | cons k ks => simp [bump]

end MetaMathlibExt.MultipleZeta

namespace MetaMathlibExt.MultipleZeta

/--
[decodeBlocks_ne_nil_of_mem_true](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/HOneBasis.lean)
-/
@[path]
private lemma decodeBlocks_ne_nil_of_mem_true (l : List Bool) (h : true ∈ l) :
  decodeBlocks l ≠ [] := by
  induction l with
  | nil => simp at h
  | cons b rest ih =>
    cases b with
    | true => simp [decodeBlocks]
    | false =>
      simp only [List.mem_cons, Bool.true_eq_false, false_or]at h
      simp only [decodeBlocks, ne_eq]
      exact bump_ne_nil_of_ne_nil _ (ih h)

end MetaMathlibExt.MultipleZeta

namespace MetaMathlibExt.MultipleZeta

/--
[decodeBlocks_append_block](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/HOneBasis.lean)
-/
@[path]
private lemma decodeBlocks_append_block (m : Nat) (R : List Bool) :
  decodeBlocks (List.replicate m false ++ [true] ++ R) =
    (m + 1) :: decodeBlocks R := by
  induction m with
  | zero => simp [decodeBlocks]
  | succ n ih =>
    change bump (decodeBlocks (List.replicate n false ++ [true] ++ R)) = _
    rw [ih]
    rfl

end MetaMathlibExt.MultipleZeta

namespace MetaMathlibExt.MultipleZeta

/--
[true_mem_of_getLast?_eq_true](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/HOneBasis.lean)
-/
@[path]
private lemma true_mem_of_getLast?_eq_true (rest : List Bool)
  (h : rest.getLast? = some true) : true ∈ rest := by
  obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp h
  rw [hys]
  exact List.mem_append_right ys (by simp)

end MetaMathlibExt.MultipleZeta

namespace MetaMathlibExt.MultipleZeta

/--
[pnat_map_val_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/HOneBasis.lean)
-/
@[path]
private lemma pnat_map_val_injective :
  Function.Injective (List.map PNat.val : List PNat → List Nat) := by
  intro l1 l2 h
  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil => rfl
    | cons j js => simp at h
  | cons k ks ih =>
    cases l2 with
    | nil => simp at h
    | cons j js =>
      simp only [List.map_cons, List.cons.injEq] at h
      obtain ⟨h1, h2⟩ := h
      rw [Subtype.ext h1, ih h2]

end MetaMathlibExt.MultipleZeta

namespace MetaMathlibExt.MultipleZeta

/--
[decode_encode_nat](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/HOneBasis.lean)
-/
@[path]
private lemma decode_encode_nat (l : List PNat) :
  decodeBlocks (encodeNatBlocks (l.map PNat.val)) = l.map PNat.val := by
  induction l with
  | nil => simp [encodeNatBlocks, decodeBlocks]
  | cons k ks ih =>
    simp only [List.map_cons, encodeNatBlocks]
    rw [decodeBlocks_append_block, ih]
    have hk : k.val - 1 + 1 = k.val := Nat.sub_add_cancel k.property
    rw [hk]

end MetaMathlibExt.MultipleZeta

namespace MetaMathlibExt.MultipleZeta

/--
[index_entries_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/HOneBasis.lean)
-/
@[path]
private lemma index_entries_injective : Function.Injective Index.entries := by
  intro a b h
  obtain ⟨n1, c1⟩ := a
  obtain ⟨n2, c2⟩ := b
  simp only [Index.entries] at h
  have hn : n1 = n2 := by
    have h1 := c1.blocks_sum
    have h2 := c2.blocks_sum
    rw [← h1, ← h2, h]
  subst hn
  have hc : c1 = c2 := Composition.ext h
  rw [hc]

end MetaMathlibExt.MultipleZeta

namespace MetaMathlibExt.MultipleZeta

/--
[pnatEntries_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/HOneBasis.lean)
-/
@[path]
private lemma pnatEntries_injective : Function.Injective Index.pnatEntries := by
  intro a b h
  have h1 := pnatEntries_val a
  have h2 := pnatEntries_val b
  rw [h] at h1
  have he : a.entries = b.entries := h1.symm.trans h2
  exact index_entries_injective he

end MetaMathlibExt.MultipleZeta

namespace MetaMathlibExt.MultipleZeta

/--
[toList_zWordPNat](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/HOneBasis.lean)
-/
@[path]
private lemma toList_zWordPNat (l : List PNat) :
  FreeMonoid.toList (zWordPNat l) = encodeNatBlocks (l.map PNat.val) := by
  induction l with
  | nil => simp [zWordPNat, encodeNatBlocks]
  | cons k ks ih =>
    have h1 : zWordPNat (k :: ks) = hoffmanBlock k * zWordPNat ks := by
      simp [zWordPNat]
    rw [h1, FreeMonoid.toList_mul, ih]
    simp [encodeNatBlocks, toList_hoffmanBlock]

end MetaMathlibExt.MultipleZeta

namespace MetaMathlibExt.MultipleZeta

/--
[zWordPNat_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/HOneBasis.lean)
-/
@[path]
private lemma zWordPNat_injective : Function.Injective zWordPNat := by
  intro l1 l2 h
  have hlist := congrArg FreeMonoid.toList h
  rw [toList_zWordPNat, toList_zWordPNat] at hlist
  have hdec : decodeBlocks (encodeNatBlocks (l1.map PNat.val)) =
    decodeBlocks (encodeNatBlocks (l2.map PNat.val)) := by rw [hlist]
  rw [decode_encode_nat, decode_encode_nat] at hdec
  exact pnat_map_val_injective hdec

end MetaMathlibExt.MultipleZeta

namespace MetaMathlibExt.MultipleZeta

/--
[zWord_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/HOneBasis.lean)
-/
@[path]
private lemma zWord_injective : Function.Injective zWord := by
  intro a b h
  have hp : a.pnatEntries = b.pnatEntries := zWordPNat_injective h
  exact pnatEntries_injective hp

end MetaMathlibExt.MultipleZeta

namespace MetaMathlibExt.MultipleZeta

/--
[mem_HOne_iff_toList](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/HOneBasis.lean)
-/
@[path]
private lemma mem_HOne_iff_toList (w : FreeMonoid Bool) :
  w ∈ wordSubmonoidHOne ↔
    FreeMonoid.toList w = [] ∨ (FreeMonoid.toList w).getLast? = some true := by
  constructor
  · intro h
    change IsHOneWord w at h
    obtain rfl | ⟨u, rfl⟩ := h
    · exact Or.inl FreeMonoid.toList_one
    · right
      have hto : FreeMonoid.toList (u * yWord) =
        FreeMonoid.toList u ++ [true] := by
        rw [FreeMonoid.toList_mul]
        rw [show FreeMonoid.toList yWord = [true] from by simp [yWord]]
      rw [hto]
      exact List.getLast?_eq_some_iff.mpr ⟨_, rfl⟩
  · intro h
    change IsHOneWord w
    obtain hnil | hlast := h
    · left
      have h1 : FreeMonoid.ofList (FreeMonoid.toList w) = w :=
        FreeMonoid.ofList_toList w
      rwa [hnil, FreeMonoid.ofList_nil] at h1
    · right
      obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp hlast
      refine ⟨FreeMonoid.ofList ys, ?_⟩
      have h1 : FreeMonoid.ofList (FreeMonoid.toList w) = w :=
        FreeMonoid.ofList_toList w
      rw [hys, FreeMonoid.ofList_append] at h1
      have hy : FreeMonoid.ofList [true] = yWord := rfl
      rwa [hy] at h1

end MetaMathlibExt.MultipleZeta

namespace MetaMathlibExt.MultipleZeta

/--
[EL_symm_single](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/HOneBasis.lean)
-/
@[path]
private lemma EL_symm_single (idx : Index) :
  freeAlgEquiv.symm (MonoidAlgebra.single (zWord idx) 1) = zMonomial idx :=
  rfl

end MetaMathlibExt.MultipleZeta

namespace MetaMathlibExt.MultipleZeta

/--
[hliM](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/HOneBasis.lean)
-/
@[path]
private lemma hliM : LinearIndependent ℚ
  (fun w : FreeMonoid Bool => MonoidAlgebra.single w (1 : ℚ)) := by
  have h := (MonoidAlgebra.basis (FreeMonoid Bool) ℚ).linearIndependent
  have h' : (⇑(MonoidAlgebra.basis (FreeMonoid Bool) ℚ)) =
    (fun w : FreeMonoid Bool => MonoidAlgebra.single w (1 : ℚ)) := by
    funext w
    exact MonoidAlgebra.basis_apply ℚ w
  rwa [h'] at h

end MetaMathlibExt.MultipleZeta

namespace MetaMathlibExt.MultipleZeta

/--
[hliZ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/HOneBasis.lean)
-/
@[path]
private lemma hliZ : LinearIndependent ℚ (fun idx : Index => zMonomial idx) := by
  have h := ((MonoidAlgebra.basis (FreeMonoid Bool) ℚ).map
    freeAlgEquiv.symm).linearIndependent.comp (fun idx : Index => zWord idx)
    zWord_injective
  have h2 : (⇑(((MonoidAlgebra.basis (FreeMonoid Bool) ℚ).map
    freeAlgEquiv.symm)) ∘ (fun idx : Index => zWord idx)) =
    (fun idx : Index => zMonomial idx) := by
    funext idx
    simp [Function.comp_apply, Module.Basis.map_apply, MonoidAlgebra.basis_apply,
      EL_symm_single]
  rwa [h2] at h

end MetaMathlibExt.MultipleZeta

namespace MetaMathlibExt.MultipleZeta

/--
[hliSub](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/HOneBasis.lean)
-/
@[path]
private lemma hliSub : LinearIndependent ℚ
  (fun idx : Index => (⟨zMonomial idx, zMonomial_mem_hOne idx⟩ : ↥hOne)) :=
  LinearIndependent.of_comp (Submodule.subtype hOne.toSubmodule) hliZ

end MetaMathlibExt.MultipleZeta

namespace MetaMathlibExt.MultipleZeta

/--
[hterm_single](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/HOneBasis.lean)
-/
@[path]
private lemma hterm_single (w : FreeMonoid Bool) (r : ℚ) :
  Finsupp.single w r = r • Finsupp.single w 1 := by
  simp

end MetaMathlibExt.MultipleZeta

namespace MetaMathlibExt.MultipleZeta

/--
[h1_finsupp](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/HOneBasis.lean)
-/
@[path]
private lemma h1_finsupp (f : FreeMonoid Bool →₀ ℚ) :
  f = ∑ w ∈ f.support, f w • Finsupp.single w 1 := by
  conv_lhs => rw [← Finsupp.sum_single f]
  apply Finset.sum_congr rfl
  intro w _
  rw [hterm_single]

end MetaMathlibExt.MultipleZeta

namespace MetaMathlibExt.MultipleZeta

/--
[hdecomp](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/HOneBasis.lean)
-/
@[path]
private lemma hdecomp (Fx : MonoidAlgebra ℚ (FreeMonoid Bool)) :
  Fx = ∑ w ∈ Fx.coeff.support, Fx.coeff w • MonoidAlgebra.single w (1 : ℚ) := by
  apply MonoidAlgebra.coeff_injective
  rw [MonoidAlgebra.coeff_sum]
  simp only [MonoidAlgebra.coeff_smul, MonoidAlgebra.coeff_single]
  exact h1_finsupp Fx.coeff

end MetaMathlibExt.MultipleZeta

/--
[hOne_basis](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/HOneBasis.lean)
-/
@[path]
private lemma hOne_basis_eq
  :
-- imply
  ∃ b : Module.Basis Index ℚ ↥hOne,
    ∀ idx : Index, (↑(b idx) : FreeAlgebra ℚ Bool) = zMonomial idx := by
-- proof
  apply MathlibExt.NumberTheory.MultipleZeta.WordAlgebraWanted.hOne_basis


-- created on 2026-10-20
-- updated on 2026-10-23
