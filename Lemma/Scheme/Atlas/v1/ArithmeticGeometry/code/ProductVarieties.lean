import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.ProductVarieties
open MvPolynomial


/--
[projLeft_append](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProductVarieties.lean)
-/
@[path]
lemma projLeft_append
  {k : Type*}
  [Field k]
  {m n : ℕ}
  {a : AffineSpace_k k m}
  {b : AffineSpace_k k n} :
-- imply
  projLeft k m n (Fin.append a b) = a := by
-- proof
  ext i
  simp [projLeft, Function.comp, Fin.append_left]

/--
[projRight_append](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProductVarieties.lean)
-/
@[path]
lemma projRight_append
  {k : Type*}
  [Field k]
  {m n : ℕ}
  {a : AffineSpace_k k m}
  {b : AffineSpace_k k n} :
-- imply
  projRight k m n (Fin.append a b) = b := by
-- proof
  ext i
  simp [projRight, Function.comp, Fin.append_right]

/--
[append_proj](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProductVarieties.lean)
-/
@[path]
lemma append_proj
  {k : Type*}
  [Field k]
  {m n : ℕ}
  {P : AffineSpace_k k (m + n)} :
-- imply
  Fin.append (projLeft k m n P) (projRight k m n P) = P := by
-- proof
  simp only [projLeft, projRight]
  exact Fin.append_castAdd_natAdd

/--
[mem_productAlgebraicSet](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProductVarieties.lean)
-/
@[path]
lemma mem_productAlgebraicSet
  {k : Type*}
  [Field k]
  {m n : ℕ}
  {S_X : Set (MvPolynomial (Fin m) (AlgebraicClosure k))}
  {S_Y : Set (MvPolynomial (Fin n) (AlgebraicClosure k))}
  {P : AffineSpace_k k (m + n)} :
-- imply
  P ∈ ProductAlgebraicSet k m n S_X S_Y ↔ projLeft k m n P ∈ AlgebraicSet k m S_X ∧ projRight k m n P ∈ AlgebraicSet k n S_Y := by
-- proof
  simp only [ProductAlgebraicSet, AlgebraicSet, Set.mem_setOf_eq,
    Set.mem_union, embedSetLeft, embedSetRight, projLeft, projRight]
  constructor
  · intro h
    constructor
    · intro f hf
      have := h (embedPolyLeft k m n f) (Or.inl ⟨f, hf, rfl⟩)
      simp only [embedPolyLeft, MvPolynomial.eval_rename] at this
      exact this
    · intro g hg
      have := h (embedPolyRight k m n g) (Or.inr ⟨g, hg, rfl⟩)
      simp only [embedPolyRight, MvPolynomial.eval_rename] at this
      exact this
  · intro ⟨hX, hY⟩ f hf
    obtain ⟨g, hg, rfl⟩ | ⟨g, hg, rfl⟩ := hf
    · simp only [embedPolyLeft, MvPolynomial.eval_rename]
      exact hX g hg
    · simp only [embedPolyRight, MvPolynomial.eval_rename]
      exact hY g hg

/--
[productAlgebraicSet_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProductVarieties.lean)
-/
@[path]
lemma productAlgebraicSet_nonempty
  {k : Type*}
  [Field k]
  {m n : ℕ}
  {S_X : Set (MvPolynomial (Fin m) (AlgebraicClosure k))}
  {S_Y : Set (MvPolynomial (Fin n) (AlgebraicClosure k))}
-- given
  (hX : (AlgebraicSet k m S_X).Nonempty)
  (hY : (AlgebraicSet k n S_Y).Nonempty) :
-- imply
  (ProductAlgebraicSet k m n S_X S_Y).Nonempty := by
-- proof
  obtain ⟨a, ha⟩ := hX
  obtain ⟨b, hb⟩ := hY
  exact ⟨Fin.append a b, (mem_productAlgebraicSet k m n S_X S_Y _).mpr
    ⟨by rwa [projLeft_append], by rwa [projRight_append]⟩⟩

/--
[eval_partialEvalRight](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProductVarieties.lean)
-/
@[path]
lemma eval_partialEvalRight
  {k : Type*}
  [Field k]
  {m n : ℕ}
  {b : AffineSpace_k k n}
  {f : MvPolynomial (Fin (m + n)) (AlgebraicClosure k)}
  {a : AffineSpace_k k m} :
-- imply
  MvPolynomial.eval a (partialEvalRight k m n b f) = MvPolynomial.eval (Fin.append a b) f := by
-- proof
  suffices h : (MvPolynomial.eval a).comp (partialEvalRight k m n b) =
    MvPolynomial.eval (Fin.append a b) from RingHom.congr_fun h f
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [partialEvalRight, MvPolynomial.eval_C]
  · intro i
    simp only [RingHom.comp_apply, partialEvalRight, MvPolynomial.eval₂Hom_X',
      MvPolynomial.eval_X]
    split_ifs with h
    · simp only [MvPolynomial.eval_X, Fin.append, Fin.addCases, h, dite_true]
      rfl
    · simp only [MvPolynomial.eval_C, Fin.append, Fin.addCases, h, dite_false]
      simp [Fin.subNat, Fin.cast]

/--
[algebraicSubset_fiber_left](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProductVarieties.lean)
-/
@[path]
lemma algebraicSubset_fiber_left
  {k : Type*}
  [Field k]
  {m n : ℕ}
  {T : Set (MvPolynomial (Fin (m + n)) (AlgebraicClosure k))}
  {b : AffineSpace_k k n} :
-- imply
  IsAlgebraicSubset k m {a : AffineSpace_k k m | Fin.append a b ∈ AlgebraicSet k (m + n) T} := by
-- proof
  refine ⟨(partialEvalRight k m n b) '' T, ?_⟩
  ext a
  simp only [AlgebraicSet, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · intro ha g hg
    obtain ⟨f, hf, rfl⟩ := hg
    rw [eval_partialEvalRight]
    exact ha f hf
  · intro ha f hf
    rw [← eval_partialEvalRight k m n b]
    exact ha _ ⟨f, hf, rfl⟩

/--
[eval_partialEvalLeft](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProductVarieties.lean)
-/
@[path]
lemma eval_partialEvalLeft
  {k : Type*}
  [Field k]
  {m n : ℕ}
  {a : AffineSpace_k k m}
  {f : MvPolynomial (Fin (m + n)) (AlgebraicClosure k)}
  {b : AffineSpace_k k n} :
-- imply
  MvPolynomial.eval b (partialEvalLeft k m n a f) = MvPolynomial.eval (Fin.append a b) f := by
-- proof
  suffices h : (MvPolynomial.eval b).comp (partialEvalLeft k m n a) =
    MvPolynomial.eval (Fin.append a b) from RingHom.congr_fun h f
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [partialEvalLeft, MvPolynomial.eval_C]
  · intro i
    simp only [RingHom.comp_apply, partialEvalLeft, MvPolynomial.eval₂Hom_X',
      MvPolynomial.eval_X]
    split_ifs with h
    · simp only [MvPolynomial.eval_C, Fin.append, Fin.addCases, h, dite_true]
      rfl
    · simp only [MvPolynomial.eval_X, Fin.append, Fin.addCases, h, dite_false]
      simp [Fin.subNat, Fin.cast]

/--
[algebraicSubset_fiber_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProductVarieties.lean)
-/
@[path]
lemma algebraicSubset_fiber_right
  {k : Type*}
  [Field k]
  {m n : ℕ}
  {T : Set (MvPolynomial (Fin (m + n)) (AlgebraicClosure k))}
  {a : AffineSpace_k k m} :
-- imply
  IsAlgebraicSubset k n {b : AffineSpace_k k n | Fin.append a b ∈ AlgebraicSet k (m + n) T} := by
-- proof
  refine ⟨(partialEvalLeft k m n a) '' T, ?_⟩
  ext b
  simp only [AlgebraicSet, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · intro hb g hg
    obtain ⟨f, hf, rfl⟩ := hg
    rw [eval_partialEvalLeft]
    exact hb f hf
  · intro hb f hf
    rw [← eval_partialEvalLeft k m n a]
    exact hb _ ⟨f, hf, rfl⟩

/--
[isAlgebraicSubset_iInter](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProductVarieties.lean)
-/
@[path]
lemma isAlgebraicSubset_iInter
  {k : Type*}
  [Field k]
  {n : ℕ}
  {V : ι → Set (AffineSpace_k k n)}
-- given
  (hV : ∀ i, IsAlgebraicSubset k n (V i)) :
-- imply
  IsAlgebraicSubset k n (⋂ i, V i) := by
-- proof
  choose S hS using hV
  refine ⟨⋃ i, S i, ?_⟩
  ext P
  simp only [Set.mem_iInter, AlgebraicSet, Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · intro hP f ⟨i, hfi⟩
    have := hP i
    rw [hS i] at this
    exact this f hfi
  · intro hP i
    rw [hS i]
    intro f hf
    exact hP f ⟨i, hf⟩

/--
[productVariety](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProductVarieties.lean)
-/
@[path]
lemma productVariety
  {k : Type*}
  [Field k]
  {m n : ℕ}
  {S_X : Set (MvPolynomial (Fin m) (AlgebraicClosure k))}
  {S_Y : Set (MvPolynomial (Fin n) (AlgebraicClosure k))}
-- given
  (hX : IsIrreducibleAlgebraicSet k m (AlgebraicSet k m S_X))
  (hY : IsIrreducibleAlgebraicSet k n (AlgebraicSet k n S_Y)) :
-- imply
  IsIrreducibleAlgebraicSet k (m + n) (ProductAlgebraicSet k m n S_X S_Y) := by
-- proof
  constructor
  · exact productAlgebraicSet_nonempty k m n S_X S_Y hX.nonempty hY.nonempty
  · intro V₁ V₂ hV₁_alg hV₂_alg hcover
    obtain ⟨T₁, hT₁⟩ := hV₁_alg
    obtain ⟨T₂, hT₂⟩ := hV₂_alg
    set X := AlgebraicSet k m S_X with hX_def
    set Y := AlgebraicSet k n S_Y with hY_def
    set XY := ProductAlgebraicSet k m n S_X S_Y with hXY_def
    have hV₁_sub_XY : V₁ ⊆ XY := by rw [hcover]; exact Set.subset_union_left
    have hV₂_sub_XY : V₂ ⊆ XY := by rw [hcover]; exact Set.subset_union_right
    have fiber_covers : ∀ b ∈ Y, ∀ a ∈ X,
      Fin.append a b ∈ V₁ ∨ Fin.append a b ∈ V₂ := by
      intro b hb a ha
      have hmem : Fin.append a b ∈ XY := by
        rw [mem_productAlgebraicSet]
        exact ⟨by rwa [projLeft_append], by rwa [projRight_append]⟩
      rwa [hcover] at hmem
    have fiber₁_alg : ∀ b, IsAlgebraicSubset k m
      {a : AffineSpace_k k m | Fin.append a b ∈ V₁} := by
      intro b; rw [hT₁]; exact algebraicSubset_fiber_left k m n T₁ b
    have fiber₂_alg : ∀ b, IsAlgebraicSubset k m
      {a : AffineSpace_k k m | Fin.append a b ∈ V₂} := by
      intro b; rw [hT₂]; exact algebraicSubset_fiber_left k m n T₂ b
    have hfib₁_sub : ∀ b, {a | Fin.append a b ∈ V₁} ⊆ X := by
      intro b a ha
      have hmem := hV₁_sub_XY ha
      rw [mem_productAlgebraicSet] at hmem
      obtain ⟨h1, _⟩ := hmem
      rwa [projLeft_append] at h1
    have hfib₂_sub : ∀ b, {a | Fin.append a b ∈ V₂} ⊆ X := by
      intro b a ha
      have hmem := hV₂_sub_XY ha
      rw [mem_productAlgebraicSet] at hmem
      obtain ⟨h1, _⟩ := hmem
      rwa [projLeft_append] at h1
    have fiber_irred : ∀ b ∈ Y,
      {a | Fin.append a b ∈ V₁} = X ∨ {a | Fin.append a b ∈ V₂} = X := by
      intro b hb
      have hcov : X ⊆ {a | Fin.append a b ∈ V₁} ∪ {a | Fin.append a b ∈ V₂} :=
        fun a ha => fiber_covers b hb a ha
      have hX_eq : X = {a | Fin.append a b ∈ V₁} ∪ {a | Fin.append a b ∈ V₂} :=
        Set.Subset.antisymm hcov (Set.union_subset (hfib₁_sub b) (hfib₂_sub b))
      exact hX.2 _ _ (fiber₁_alg b) (fiber₂_alg b) hX_eq
    set Y₁ := ⋂ (a : X), {b : AffineSpace_k k n | Fin.append a.1 b ∈ V₁} with hY₁_def
    set Y₂ := ⋂ (a : X), {b : AffineSpace_k k n | Fin.append a.1 b ∈ V₂} with hY₂_def
    have hY₁_alg : IsAlgebraicSubset k n Y₁ := by
      apply isAlgebraicSubset_iInter
      intro ⟨a, _⟩
      rw [hT₁]
      exact algebraicSubset_fiber_right k m n T₁ a
    have hY₂_alg : IsAlgebraicSubset k n Y₂ := by
      apply isAlgebraicSubset_iInter
      intro ⟨a, _⟩
      rw [hT₂]
      exact algebraicSubset_fiber_right k m n T₂ a
    have hY₁_sub : Y₁ ⊆ Y := by
      intro b hb
      obtain ⟨a, ha⟩ := hX.nonempty
      have := Set.mem_iInter.mp hb ⟨a, ha⟩
      simp only [Set.mem_setOf_eq] at this
      have hmem := hV₁_sub_XY this
      rw [mem_productAlgebraicSet] at hmem
      obtain ⟨_, h2⟩ := hmem
      rwa [projRight_append] at h2
    have hY₂_sub : Y₂ ⊆ Y := by
      intro b hb
      obtain ⟨a, ha⟩ := hX.nonempty
      have := Set.mem_iInter.mp hb ⟨a, ha⟩
      simp only [Set.mem_setOf_eq] at this
      have hmem := hV₂_sub_XY this
      rw [mem_productAlgebraicSet] at hmem
      obtain ⟨_, h2⟩ := hmem
      rwa [projRight_append] at h2
    have hY_cover : Y = Y₁ ∪ Y₂ := by
      ext b
      constructor
      · intro hb
        obtain h | h := fiber_irred b hb
        · left
          rw [hY₁_def]
          simp only [Set.mem_iInter, Set.mem_setOf_eq]
          intro ⟨a, ha⟩
          have := h.symm ▸ ha
          exact this
        · right
          rw [hY₂_def]
          simp only [Set.mem_iInter, Set.mem_setOf_eq]
          intro ⟨a, ha⟩
          have := h.symm ▸ ha
          exact this
      · intro hb
        obtain hb | hb := hb
        · exact hY₁_sub hb
        · exact hY₂_sub hb
    obtain h | h := hY.2 Y₁ Y₂ hY₁_alg hY₂_alg hY_cover
    ·
      left
      apply Set.Subset.antisymm hV₁_sub_XY
      intro P hP
      rw [mem_productAlgebraicSet] at hP
      obtain ⟨hPX, hPY⟩ := hP
      have hb_in_Y₁ : projRight k m n P ∈ Y₁ := h ▸ hPY
      have := Set.mem_iInter.mp hb_in_Y₁ ⟨projLeft k m n P, hPX⟩
      simp only [Set.mem_setOf_eq] at this
      rwa [append_proj] at this
    ·
      right
      apply Set.Subset.antisymm hV₂_sub_XY
      intro P hP
      rw [mem_productAlgebraicSet] at hP
      obtain ⟨hPX, hPY⟩ := hP
      have hb_in_Y₂ : projRight k m n P ∈ Y₂ := h ▸ hPY
      have := Set.mem_iInter.mp hb_in_Y₂ ⟨projLeft k m n P, hPX⟩
      simp only [Set.mem_setOf_eq] at this
      rwa [append_proj] at this

/--
[subset_vanishingIdeal_algebraicSet](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProductVarieties.lean)
-/
@[path]
lemma subset_vanishingIdeal_algebraicSet
  {k : Type*}
  [Field k]
  {n : ℕ}
  {S : Set (MvPolynomial (Fin n) (AlgebraicClosure k))} :
-- imply
  S ⊆ ↑(vanishingIdeal_kbar k n (AlgebraicSet k n S)) := by
-- proof
  intro f hf P hP
  exact hP f hf

/--
[algebraicSet_anti](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProductVarieties.lean)
-/
@[path]
lemma algebraicSet_anti
  {k : Type*}
  [Field k]
  {n : ℕ}
  {S T : Set (MvPolynomial (Fin n) (AlgebraicClosure k))}
-- given
  (h : S ⊆ T) :
-- imply
  AlgebraicSet k n T ⊆ AlgebraicSet k n S := by
-- proof
  intro P hP f hf
  exact hP f (h hf)

/--
[subset_algebraicSet_vanishingIdeal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProductVarieties.lean)
-/
@[path]
lemma subset_algebraicSet_vanishingIdeal
  {k : Type*}
  [Field k]
  {n : ℕ}
  {V : Set (AffineSpace_k k n)} :
-- imply
  V ⊆ AlgebraicSet k n ↑(vanishingIdeal_kbar k n V) := by
-- proof
  intro P hP f hf
  exact hf P hP

/--
[algebraicSet_vanishingIdeal_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProductVarieties.lean)
-/
@[path]
lemma algebraicSet_vanishingIdeal_eq
  {k : Type*}
  [Field k]
  {n : ℕ}
  {S : Set (MvPolynomial (Fin n) (AlgebraicClosure k))} :
-- imply
  AlgebraicSet k n ↑(vanishingIdeal_kbar k n (AlgebraicSet k n S)) = AlgebraicSet k n S :=
-- proof
  Set.Subset.antisymm
    (algebraicSet_anti k n (subset_vanishingIdeal_algebraicSet k n S))
    (subset_algebraicSet_vanishingIdeal k n (AlgebraicSet k n S))

/--
[vanishingIdeal_kbar_anti](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProductVarieties.lean)
-/
@[path]
lemma vanishingIdeal_kbar_anti
  {k : Type*}
  [Field k]
  {n : ℕ}
  {V W : Set (AffineSpace_k k n)}
-- given
  (h : V ⊆ W) :
-- imply
  vanishingIdeal_kbar k n W ≤ vanishingIdeal_kbar k n V := by
-- proof
  intro f hf P hP
  exact hf P (h hP)

/--
[vanishingIdeal_kbar_injective_on_algebraicSets](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProductVarieties.lean)
-/
@[path]
lemma vanishingIdeal_kbar_injective_on_algebraicSets
  {k : Type*}
  [Field k]
  {n : ℕ}
  {S₁ S₂ : Set (MvPolynomial (Fin n) (AlgebraicClosure k))}
-- given
  (heq : vanishingIdeal_kbar k n (AlgebraicSet k n S₁) = vanishingIdeal_kbar k n (AlgebraicSet k n S₂)) :
-- imply
  AlgebraicSet k n S₁ = AlgebraicSet k n S₂ := by
-- proof
  rw [← algebraicSet_vanishingIdeal_eq k n S₁, ← algebraicSet_vanishingIdeal_eq k n S₂, heq]

/--
[vanishingIdeal_kbar_strictAnti_algebraicSets](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProductVarieties.lean)
-/
@[path]
lemma vanishingIdeal_kbar_strictAnti_algebraicSets
  {k : Type*}
  [Field k]
  {n : ℕ}
  {S₁ S₂ : Set (MvPolynomial (Fin n) (AlgebraicClosure k))}
-- given
  (h : AlgebraicSet k n S₁ ⊂ AlgebraicSet k n S₂) :
-- imply
  vanishingIdeal_kbar k n (AlgebraicSet k n S₂) < vanishingIdeal_kbar k n (AlgebraicSet k n S₁) := by
-- proof
  refine lt_of_le_of_ne (vanishingIdeal_kbar_anti k n h.le) ?_
  intro heq
  exact h.ne (vanishingIdeal_kbar_injective_on_algebraicSets k n heq.symm)

/--
[vanishingIdeal_kbar_injective_closeds](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProductVarieties.lean)
-/
@[path]
lemma vanishingIdeal_kbar_injective_closeds
  {k : Type*}
  [Field k]
  {n : ℕ}
  {V₁ V₂ : Set (AffineSpace_k k n)}
-- given
  (hV₁ : IsAlgebraicSetAffine k n V₁)
  (hV₂ : IsAlgebraicSetAffine k n V₂)
  (heq : vanishingIdeal_kbar k n V₁ = vanishingIdeal_kbar k n V₂) :
-- imply
  V₁ = V₂ := by
-- proof
  obtain ⟨S₁, rfl⟩ := hV₁
  obtain ⟨S₂, rfl⟩ := hV₂
  exact vanishingIdeal_kbar_injective_on_algebraicSets k n heq

/--
[affineSpace_noetherianSpace](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProductVarieties.lean)
-/
@[path]
lemma affineSpace_noetherianSpace
  {k : Type*}
  [Field k]
  {n : ℕ} :
-- imply
  @TopologicalSpace.NoetherianSpace _ (zariskiTopology k n) := by
-- proof
  letI inst : TopologicalSpace (AffineSpace_k k n) := zariskiTopology k n
  exact ((TopologicalSpace.noetherianSpace_TFAE (AffineSpace_k k n)).out 0 1).mpr <| by
    constructor
    apply Subrelation.wf (r := InvImage (· > ·) (fun C : TopologicalSpace.Closeds (AffineSpace_k k n) =>
      vanishingIdeal_kbar k n C.carrier))
    ·
      intro ⟨a, ha⟩ ⟨b, hb⟩ (hab : (⟨a, ha⟩ : TopologicalSpace.Closeds _) < ⟨b, hb⟩)
      show vanishingIdeal_kbar k n a > vanishingIdeal_kbar k n b
      have ha' := (isClosed_zariskiTopology_iff_isAlgebraicSet k n a).mp ha
      have hb' := (isClosed_zariskiTopology_iff_isAlgebraicSet k n b).mp hb
      have hab_sub : a ⊆ b := hab.le
      have h_le : vanishingIdeal_kbar k n b ≤ vanishingIdeal_kbar k n a :=
        vanishingIdeal_kbar_anti k n hab_sub
      have h_ne : vanishingIdeal_kbar k n a ≠ vanishingIdeal_kbar k n b := by
        intro heq
        have := vanishingIdeal_kbar_injective_closeds k n ha' hb' heq
        exact hab.ne (SetLike.ext' this)
      exact lt_of_le_of_ne h_le h_ne.symm
    ·
      exact InvImage.wf _ (IsNoetherian.wf inferInstance)

/--
[affineSpace_quasiCompact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProductVarieties.lean)
-/
@[path]
lemma affineSpace_quasiCompact
  {k : Type*}
  [Field k]
  {n : ℕ}
  {S : Set (AffineSpace_k k n)} :
-- imply
  @IsCompact _ (zariskiTopology k n) S := by
-- proof
  letI : TopologicalSpace (AffineSpace_k k n) := zariskiTopology k n
  haveI := affineSpace_noetherianSpace k n
  exact TopologicalSpace.NoetherianSpace.isCompact S
section Lemma163
open MvPolynomial
variable {k} {n : ℕ}

/--
[evalOnCoordinateRingBar_mk](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProductVarieties.lean)
-/
@[path]
lemma evalOnCoordinateRingBar_mk
  {k : Type*}
  [Field k]
  {k}
  {n : ℕ}
  {V : Set (AffineSpace_k k n)}
  {P : AffineSpace_k k n}
  {f : MvPolynomial (Fin n) (AlgebraicClosure k)}
-- given
  (hP : P ∈ V) :
-- imply
  evalOnCoordinateRingBar V P hP (Ideal.Quotient.mk _ f) = MvPolynomial.eval P f :=
-- proof
  Ideal.Quotient.lift_mk _ _ _

/--
[evalOnCoordinateRingBar_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProductVarieties.lean)
-/
@[path]
lemma evalOnCoordinateRingBar_surjective
  {k : Type*}
  [Field k]
  {k}
  {n : ℕ}
  {V : Set (AffineSpace_k k n)}
  {P : AffineSpace_k k n}
-- given
  (hP : P ∈ V) :
-- imply
  Function.Surjective (evalOnCoordinateRingBar V P hP) := by
-- proof
  intro c
  exact ⟨Ideal.Quotient.mk _ (MvPolynomial.C c), by
    rw [evalOnCoordinateRingBar_mk, MvPolynomial.eval_C]⟩

/--
[maximalIdealOfPoint_isMaximal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProductVarieties.lean)
-/
@[path]
lemma maximalIdealOfPoint_isMaximal
  {k : Type*}
  [Field k]
  {k}
  {n : ℕ}
  {V : Set (AffineSpace_k k n)}
  {P : AffineSpace_k k n}
-- given
  (hP : P ∈ V) :
-- imply
  (maximalIdealOfPoint V P hP).IsMaximal :=
-- proof
  RingHom.ker_isMaximal_of_surjective _ (evalOnCoordinateRingBar_surjective V P hP)

/--
[comap_maximalIdealOfPoint_eq_ker_eval](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProductVarieties.lean)
-/
@[path]
lemma comap_maximalIdealOfPoint_eq_ker_eval
  {k : Type*}
  [Field k]
  {k}
  {n : ℕ}
  {V : Set (AffineSpace_k k n)}
  {P : AffineSpace_k k n}
-- given
  (hP : P ∈ V) :
-- imply
  Ideal.comap (Ideal.Quotient.mk (idealOfAlgebraicSet V)) (maximalIdealOfPoint V P hP) = RingHom.ker (MvPolynomial.eval P) := by
-- proof
  ext f
  simp only [maximalIdealOfPoint, Ideal.mem_comap, RingHom.mem_ker]
  change evalOnCoordinateRingBar V P hP (Ideal.Quotient.mk _ f) = 0 ↔ _
  rw [evalOnCoordinateRingBar_mk]

/--
[maximalIdealOfPoint_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProductVarieties.lean)
-/
@[path]
lemma maximalIdealOfPoint_injective
  {k : Type*}
  [Field k]
  {k}
  {n : ℕ}
  {V : Set (AffineSpace_k k n)}
  {P₁ P₂ : AffineSpace_k k n}
-- given
  (hP₁ : P₁ ∈ V)
  (hP₂ : P₂ ∈ V)
  (heq : maximalIdealOfPoint V P₁ hP₁ = maximalIdealOfPoint V P₂ hP₂) :
-- imply
  P₁ = P₂ := by
-- proof
  have hker : RingHom.ker (MvPolynomial.eval P₁) =
    RingHom.ker (MvPolynomial.eval (R := AlgebraicClosure k) P₂) := by
    rw [← comap_maximalIdealOfPoint_eq_ker_eval V P₁ hP₁,
      ← comap_maximalIdealOfPoint_eq_ker_eval V P₂ hP₂, heq]
  ext i
  have hmem : MvPolynomial.X i - MvPolynomial.C (P₁ i) ∈
    RingHom.ker (MvPolynomial.eval (R := AlgebraicClosure k) P₁) := by
    simp [RingHom.mem_ker]
  rw [hker] at hmem
  simp [RingHom.mem_ker] at hmem
  exact (sub_eq_zero.mp hmem).symm

/--
[idealOfAlgebraicSet_le_vanishingIdeal_singleton_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProductVarieties.lean)
-/
@[path]
lemma idealOfAlgebraicSet_le_vanishingIdeal_singleton_iff
  {k : Type*}
  [Field k]
  {k}
  {n : ℕ}
  {V : Set (AffineSpace_k k n)}
  {P : AffineSpace_k k n}
-- given
  (hV : IsAlgebraicSubset k n V) :
-- imply
  idealOfAlgebraicSet V ≤ MvPolynomial.vanishingIdeal (AlgebraicClosure k) ({P} : Set (AffineSpace_k k n)) ↔ P ∈ V := by
-- proof
  rw [idealOfAlgebraicSet_eq_vanishingIdeal]
  constructor
  · intro h
    obtain ⟨S, rfl⟩ := hV
    intro f hf
    have hfV : f ∈ MvPolynomial.vanishingIdeal (AlgebraicClosure k)
      (AlgebraicSet k n S) := by
      rw [MvPolynomial.mem_vanishingIdeal_iff]
      intro Q hQ
      rw [MvPolynomial.aeval_eq_eval]
      exact hQ f hf
    have hfP := h hfV
    rw [MvPolynomial.mem_vanishingIdeal_iff] at hfP
    have := hfP P (Set.mem_singleton P)
    rwa [MvPolynomial.aeval_eq_eval] at this
  · intro hP f hf
    rw [MvPolynomial.mem_vanishingIdeal_iff] at hf ⊢
    intro Q hQ
    rw [Set.mem_singleton_iff] at hQ
    subst hQ
    exact hf Q hP

/--
[lemma_16_3](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProductVarieties.lean)
-/
@[path]
lemma lemma_16_3
  {k : Type*}
  [Field k]
  {k}
  {n : ℕ}
  {V : Set (AffineSpace_k k n)}
-- given
  (hV : IsAlgebraicSubset k n V) :
-- imply
  Function.Bijective (fun (Pt : V) => ⟨maximalIdealOfPoint V Pt.1 Pt.2, maximalIdealOfPoint_isMaximal V Pt.1 Pt.2⟩ : V → {m : Ideal (AffineCoordinateRingBar V) // m.IsMaximal}) := by
-- proof
  constructor
  ·
    intro ⟨P₁, hP₁⟩ ⟨P₂, hP₂⟩ heq
    simp only [Subtype.mk.injEq] at heq
    exact Subtype.ext (maximalIdealOfPoint_injective V P₁ P₂ hP₁ hP₂ heq)
  ·
    intro ⟨mbar, hmbar⟩
    set m := Ideal.comap (Ideal.Quotient.mk (idealOfAlgebraicSet V)) mbar
    have hm_max : m.IsMaximal := by
      unfold AffineCoordinateRingBar at mbar hmbar
      haveI : mbar.IsMaximal := hmbar
      exact Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
    obtain ⟨P, hP_eq⟩ := maximal_ideal_eq_vanishingIdeal_singleton k m hm_max
    have hIV_le_m : idealOfAlgebraicSet V ≤ m := by
      intro f hf
      show Ideal.Quotient.mk (idealOfAlgebraicSet V) f ∈ mbar
      have : Ideal.Quotient.mk (idealOfAlgebraicSet V) f = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr hf
      rwa [this]
    rw [hP_eq] at hIV_le_m
    have hPV : P ∈ V :=
      (idealOfAlgebraicSet_le_vanishingIdeal_singleton_iff V hV P).mp hIV_le_m
    use ⟨P, hPV⟩
    simp only [Subtype.mk.injEq]
    have hinj : Function.Injective
      (Ideal.comap (Ideal.Quotient.mk (idealOfAlgebraicSet V)) :
        Ideal (AffineCoordinateRingBar V) →
        Ideal (MvPolynomial (Fin n) (AlgebraicClosure k))) := by
      intro I₁ I₂ h
      have hsurj : ∀ (I : Ideal (AffineCoordinateRingBar V)),
        Ideal.map (Ideal.Quotient.mk (idealOfAlgebraicSet V))
          (Ideal.comap (Ideal.Quotient.mk (idealOfAlgebraicSet V)) I) = I :=
        Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective
      rw [← hsurj I₁, ← hsurj I₂, h]
    apply hinj
    rw [comap_maximalIdealOfPoint_eq_ker_eval]
    show RingHom.ker (MvPolynomial.eval P) = m
    rw [hP_eq, ker_eval_eq_vanishingIdeal_singleton k P]
end Lemma163
open MvPolynomial

/--
[mem_productProjectiveAlgebraicSet](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProductVarieties.lean)
-/
@[path]
lemma mem_productProjectiveAlgebraicSet
  {k : Type*}
  [Field k]
  [Field k]
  {m n : ℕ}
  {S_X : Set (HomogPoly k m)}
  {S_Y : Set (HomogPoly k n)}
  {PQ : ProductProjectiveSpace k m n} :
-- imply
  PQ ∈ ProductProjectiveAlgebraicSet m n S_X S_Y ↔ PQ.1 ∈ ProjVanishingSet k m S_X ∧ PQ.2 ∈ ProjVanishingSet k n S_Y := by
-- proof
  obtain ⟨P, Q⟩ := PQ
  obtain ⟨v, rfl⟩ := P.exists_rep
  obtain ⟨w, rfl⟩ := Q.exists_rep
  simp only [ProductProjectiveAlgebraicSet, Set.mem_setOf_eq,
    ProjVanishingSet, Quotient.liftOn_mk]
  constructor
  · intro h
    exact ⟨fun f hf => by
      have := h _ (Set.mem_union_left _ ⟨f.poly, ⟨f, hf, rfl⟩, rfl⟩)
      rwa [eval_embedHomogPolyLeft] at this,
    fun f hf => by
      have := h _ (Set.mem_union_right _ ⟨f.poly, ⟨f, hf, rfl⟩, rfl⟩)
      rwa [eval_embedHomogPolyRight] at this⟩
  · intro ⟨hP, hQ⟩ f hf
    simp only [combinedHomogPolySet, Set.mem_union, embedHomogSetLeft, embedHomogSetRight,
      Set.mem_image] at hf
    obtain ⟨p, ⟨g, hgS, rfl⟩, rfl⟩ | ⟨q, ⟨g, hgS, rfl⟩, rfl⟩ := hf
    · rw [eval_embedHomogPolyLeft]; exact hP g hgS
    · rw [eval_embedHomogPolyRight]; exact hQ g hgS

/--
[idealOfAlgebraicSet_le_ker_eval](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProductVarieties.lean)
-/
@[path]
private lemma idealOfAlgebraicSet_le_ker_eval_eq
  {k : Type*}
  [Field k]
  {k}
  {n : ℕ}
  {V : Set (AffineSpace_k k n)}
  {P : AffineSpace_k k n}
-- given
  (hP : P ∈ V) :
-- imply
  idealOfAlgebraicSet V ≤ RingHom.ker (MvPolynomial.eval P) := by
-- proof
  apply idealOfAlgebraicSet_le_ker_eval k V P hP

/--
[eval_embedHomogPolyLeft](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProductVarieties.lean)
-/
@[path]
private lemma eval_embedHomogPolyLeft_eq
  {k : Type*}
  [Field k]
  [Field k]
  {m n : ℕ}
  {p : MvPolynomial (Fin (m + 1)) (AlgebraicClosure k)}
  {a : Fin (m + 1) → AlgebraicClosure k}
  {b : Fin (n + 1) → AlgebraicClosure k} :
-- imply
  eval (Fin.append a b) (embedHomogPolyLeft m n p) = eval a p := by
-- proof
  apply eval_embedHomogPolyLeft k m n p a b

/--
[eval_embedHomogPolyRight](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProductVarieties.lean)
-/
@[path]
private lemma eval_embedHomogPolyRight_eq
  {k : Type*}
  [Field k]
  [Field k]
  {m n : ℕ}
  {p : MvPolynomial (Fin (n + 1)) (AlgebraicClosure k)}
  {a : Fin (m + 1) → AlgebraicClosure k}
  {b : Fin (n + 1) → AlgebraicClosure k} :
-- imply
  eval (Fin.append a b) (embedHomogPolyRight m n p) = eval b p := by
-- proof
  apply eval_embedHomogPolyRight k m n p a b

/--
[combinedHomogPolySet_vanish_of_rescale](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProductVarieties.lean)
-/
@[path]
private lemma combinedHomogPolySet_vanish_of_rescale_eq
  {k : Type*}
  [Field k]
  [Field k]
  {m n : ℕ}
  {S_X : Set (HomogPoly k m)}
  {S_Y : Set (HomogPoly k n)}
  {a₁ : Fin (m + 1) → AlgebraicClosure k}
  {b₁ : Fin (n + 1) → AlgebraicClosure k}
  {a₂ : Fin (m + 1) → AlgebraicClosure k}
  {b₂ : Fin (n + 1) → AlgebraicClosure k}
  {c d : AlgebraicClosure k}
-- given
  (hc : c ≠ 0)
  (hd : d ≠ 0)
  (ha : a₁ = fun i => c * a₂ i)
  (hb : b₁ = fun i => d * b₂ i)
  (h : ∀ f ∈ combinedHomogPolySet m n S_X S_Y, eval (Fin.append a₁ b₁) f = 0) :
-- imply
  ∀ f ∈ combinedHomogPolySet m n S_X S_Y, eval (Fin.append a₂ b₂) f = 0 := by
-- proof
  apply combinedHomogPolySet_vanish_of_rescale k hc hd ha hb h


-- created on 2026-10-23
