import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.NumberTheory.MultipleZeta.HZeroBasis.Part3
open MetaMathlibExt.MultipleZeta
open MathlibExt.NumberTheory.MultipleZeta.WordAlgebraWanted


namespace MathlibExt.NumberTheory.MultipleZeta.WordAlgebraWanted

/--
[decAux_replicate](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/HZeroBasis.lean)
-/
@[path]
private lemma decAux_replicate (j : Nat) (rest : List Bool) (n : Nat) :
  decAux (List.replicate j false ++ rest) n = decAux rest (n + j) := by
  induction j generalizing n rest with
  | zero => simp
  | succ j ih =>
    rw [List.replicate_succ, List.cons_append]
    have e : decAux (false :: (List.replicate j false ++ rest)) n
      = decAux (List.replicate j false ++ rest) (n + 1) := rfl
    rw [e, ih]
    congr 1
    omega

end MathlibExt.NumberTheory.MultipleZeta.WordAlgebraWanted

namespace MathlibExt.NumberTheory.MultipleZeta.WordAlgebraWanted

/--
[decAux_encode](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/HZeroBasis.lean)
-/
@[path]
private lemma decAux_encode (l : List Nat) (hpos : ∀ x ∈ l, 0 < x) :
  decAux (encList l) 0 = l := by
  induction l with
  | nil => rfl
  | cons k ks ih =>
    have hk : 0 < k := hpos k (by simp)
    have hks : ∀ x ∈ ks, 0 < x :=
      fun x hx => hpos x (List.mem_cons_of_mem k hx)
    have e1 : encList (k :: ks)
      = List.replicate (k - 1) false ++ ([true] ++ encList ks) := by
      simp [encList, encBlock, List.append_assoc]
    rw [e1, decAux_replicate]
    have e2 : (0 : Nat) + (k - 1) = k - 1 := Nat.zero_add _
    rw [e2]
    have e3 : decAux ([true] ++ encList ks) (k - 1)
      = k :: decAux (encList ks) 0 := by
      rw [List.singleton_append]
      change (k - 1 + 1) :: decAux (encList ks) 0 = k :: decAux (encList ks) 0
      rw [Nat.sub_add_cancel hk]
    rw [e3, ih hks]

end MathlibExt.NumberTheory.MultipleZeta.WordAlgebraWanted

namespace MathlibExt.NumberTheory.MultipleZeta.WordAlgebraWanted

/--
[encList_inj](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/HZeroBasis.lean)
-/
@[path]
private lemma encList_inj (l1 : List Nat) (h1 : ∀ x ∈ l1, 0 < x)
  (l2 : List Nat) (h2 : ∀ x ∈ l2, 0 < x)
  (h : encList l1 = encList l2) : l1 = l2 := by
  have e1 := decAux_encode l1 h1
  have e2 := decAux_encode l2 h2
  rw [h] at e1
  exact e1.symm.trans e2

end MathlibExt.NumberTheory.MultipleZeta.WordAlgebraWanted

namespace MathlibExt.NumberTheory.MultipleZeta.WordAlgebraWanted

/--
[entries_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/HZeroBasis.lean)
-/
@[path]
private lemma entries_pos (idx : Index) : ∀ x ∈ idx.entries, 0 < x := by
  obtain ⟨n, c⟩ := idx
  simp only [Index.entries]
  exact fun x hx => c.blocks_pos hx

end MathlibExt.NumberTheory.MultipleZeta.WordAlgebraWanted

namespace MathlibExt.NumberTheory.MultipleZeta.WordAlgebraWanted

/--
[entries_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/HZeroBasis.lean)
-/
@[path]
private lemma entries_injective : Function.Injective Index.entries := by
  intro a b h
  obtain ⟨n1, c1⟩ := a
  obtain ⟨n2, c2⟩ := b
  simp only [Index.entries] at h
  have hn : n1 = n2 := by rw [← c1.blocks_sum, ← c2.blocks_sum, h]
  subst hn
  have hc : c1 = c2 := Composition.ext h
  subst hc
  rfl

end MathlibExt.NumberTheory.MultipleZeta.WordAlgebraWanted

namespace MathlibExt.NumberTheory.MultipleZeta.WordAlgebraWanted

/--
[hZeroLI](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/HZeroBasis.lean)
-/
@[path]
private lemma hZeroLI :
  LinearIndependent ℚ (fun idx : HZeroIndex => zMonomial idx.val) := by
  have hzw : Function.Injective (fun idx : HZeroIndex => zWord idx.val) :=
    zWord_injective.comp Subtype.val_injective
  have hF : LinearIndependent ℚ
    (fun w : FreeMonoid Bool => Finsupp.single w (1 : ℚ)) :=
    Finsupp.linearIndependent_single_one ℚ _
  have hker2 : LinearMap.ker
    (MonoidAlgebra.coeffLinearEquiv (R := ℚ) (S := ℚ) (M := FreeMonoid Bool)).symm.toLinearMap
    = ⊥ :=
    LinearMap.ker_eq_bot.mpr
      (MonoidAlgebra.coeffLinearEquiv (R := ℚ) (S := ℚ) (M := FreeMonoid Bool)).symm.injective
  have hmap : LinearIndependent ℚ
    (⇑(MonoidAlgebra.coeffLinearEquiv (R := ℚ) (S := ℚ)
      (M := FreeMonoid Bool)).symm.toLinearMap ∘
      fun w : FreeMonoid Bool => Finsupp.single w (1 : ℚ)) :=
    hF.map (f := (MonoidAlgebra.coeffLinearEquiv (R := ℚ) (S := ℚ)
      (M := FreeMonoid Bool)).symm.toLinearMap)
      (by rw [hker2]; exact disjoint_bot_right)
  have hsingle : ∀ w : FreeMonoid Bool,
    (MonoidAlgebra.coeffLinearEquiv (R := ℚ) (S := ℚ)
      (M := FreeMonoid Bool)).symm.toLinearMap (Finsupp.single w (1 : ℚ))
      = MonoidAlgebra.single w 1 := by
    intro w
    have e1 : (MonoidAlgebra.coeffLinearEquiv (R := ℚ) (S := ℚ)
      (M := FreeMonoid Bool)).symm (Finsupp.single w (1 : ℚ))
      = MonoidAlgebra.single w 1 := by
      rw [MonoidAlgebra.coeffLinearEquiv_symm_apply, MonoidAlgebra.ofCoeff_single]
    exact e1
  have hM : LinearIndependent ℚ
    (fun w : FreeMonoid Bool => MonoidAlgebra.single w (1 : ℚ)) := by
    have e : (⇑(MonoidAlgebra.coeffLinearEquiv (R := ℚ) (S := ℚ)
      (M := FreeMonoid Bool)).symm.toLinearMap ∘
      fun w : FreeMonoid Bool => Finsupp.single w (1 : ℚ))
      = (fun w : FreeMonoid Bool => MonoidAlgebra.single w (1 : ℚ)) :=
      funext fun w => hsingle w
    rwa [e] at hmap
  have hcomp : LinearIndependent ℚ
    ((fun w : FreeMonoid Bool => MonoidAlgebra.single w (1 : ℚ)) ∘
      fun idx : HZeroIndex => zWord idx.val) :=
    hM.comp _ hzw
  have hkerE : LinearMap.ker
    (FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := ℚ) (X := Bool)).symm.toLinearEquiv.toLinearMap
    = ⊥ :=
    LinearMap.ker_eq_bot.mpr
      (FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := ℚ) (X := Bool)).symm.toLinearEquiv.injective
  have hVmap : LinearIndependent ℚ
    (⇑(FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := ℚ)
      (X := Bool)).symm.toLinearEquiv.toLinearMap ∘
      ((fun w : FreeMonoid Bool => MonoidAlgebra.single w (1 : ℚ)) ∘
        fun idx : HZeroIndex => zWord idx.val)) :=
    hcomp.map (f := (FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := ℚ)
      (X := Bool)).symm.toLinearEquiv.toLinearMap)
      (by rw [hkerE]; exact disjoint_bot_right)
  have hconv : (⇑(FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := ℚ)
    (X := Bool)).symm.toLinearEquiv.toLinearMap ∘
    ((fun w : FreeMonoid Bool => MonoidAlgebra.single w (1 : ℚ)) ∘
      fun idx : HZeroIndex => zWord idx.val))
    = (fun idx : HZeroIndex => zMonomial idx.val) := by
    funext idx
    rfl
  rwa [hconv] at hVmap

end MathlibExt.NumberTheory.MultipleZeta.WordAlgebraWanted

namespace MathlibExt.NumberTheory.MultipleZeta.WordAlgebraWanted

/--
[hZero_basis](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/HZeroBasis.lean)
-/
@[path]
lemma hZero_basis
  :
-- imply
  ∃ b : Module.Basis HZeroIndex ℚ ↥hZero,
    ∀ idx : HZeroIndex, (↑(b idx) : FreeAlgebra ℚ Bool) = zMonomial idx.val := by
-- proof
  refine ⟨(Module.Basis.span hZeroLI).map spanEquivHZero, fun idx => ?_⟩
  rw [Module.Basis.map_apply]
  exact congrArg Subtype.val (Module.Basis.span_apply hZeroLI idx)

end MathlibExt.NumberTheory.MultipleZeta.WordAlgebraWanted


-- created on 2026-10-20
-- updated on 2026-10-26
