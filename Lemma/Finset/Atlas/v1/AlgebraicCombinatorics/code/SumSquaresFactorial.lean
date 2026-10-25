import Mathlib
import sympy.Basic
import Def.v1.Atlas.AlgebraicCombinatorics.code.SumSquaresFactorial
open HasseWalkFormula HasseWalks
open scoped Nat


/--
[young_cell_fst_lt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/SumSquaresFactorial.lean)
-/
@[path]
lemma young_cell_fst_lt
  {μ : YoungDiagram}
  {i j : ℕ}
-- given
  (h : (i, j) ∈ μ) :
-- imply
  i < μ.card := by
-- proof
  have hmem : ∀ r ∈ Finset.range (i + 1), (r, (0 : ℕ)) ∈ μ.cells :=
    fun r hr => by
      simp only [Finset.mem_range] at hr
      exact μ.up_left_mem (by omega) (Nat.zero_le j) h
  have hinj : Set.InjOn (fun r => (r, (0 : ℕ))) (↑(Finset.range (i + 1)) : Set ℕ) :=
    fun a _ b _ hab => (Prod.mk.inj hab).1
  have hle : (Finset.range (i + 1)).card ≤ μ.cells.card :=
    Finset.card_le_card_of_injOn (fun r => (r, (0 : ℕ)))
      (fun r hr => hmem r hr) hinj
  simpa [Finset.card_range] using hle

/--
[young_cell_snd_lt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/SumSquaresFactorial.lean)
-/
@[path]
lemma young_cell_snd_lt
  {μ : YoungDiagram}
  {i j : ℕ}
-- given
  (h : (i, j) ∈ μ) :
-- imply
  j < μ.card := by
-- proof
  have hmem : ∀ c ∈ Finset.range (j + 1), ((0 : ℕ), c) ∈ μ.cells :=
    fun c hc => by
      simp only [Finset.mem_range] at hc
      exact μ.up_left_mem (Nat.zero_le i) (by omega) h
  have hinj : Set.InjOn (fun c => ((0 : ℕ), c)) (↑(Finset.range (j + 1)) : Set ℕ) :=
    fun a _ b _ hab => (Prod.mk.inj hab).2
  have hle : (Finset.range (j + 1)).card ≤ μ.cells.card :=
    Finset.card_le_card_of_injOn (fun c => ((0 : ℕ), c))
      (fun c hc => hmem c hc) hinj
  simpa [Finset.card_range] using hle

/--
[YoungDiagram.cells_subset_range_sq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/SumSquaresFactorial.lean)
-/
@[path]
lemma YoungDiagram.cells_subset_range_sq
  {μ : YoungDiagram} :
-- imply
  μ.cells ⊆ Finset.range μ.card ×ˢ Finset.range μ.card := by
-- proof
  intro ⟨i, j⟩ hcell
  simp only [Finset.mem_product, Finset.mem_range]
  exact ⟨young_cell_fst_lt hcell, young_cell_snd_lt hcell⟩

/--
[mem_youngDiagramsOfSize](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/SumSquaresFactorial.lean)
-/
@[path]
lemma mem_youngDiagramsOfSize
  {n : ℕ}
  {μ : YoungDiagram} :
-- imply
  μ ∈ youngDiagramsOfSize n ↔ μ.card = n := by
-- proof
  simp [youngDiagramsOfSize, Set.Finite.mem_toFinset]

/--
[WalkTypeCount.applyStepWord_append](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/SumSquaresFactorial.lean)
-/
@[path]
lemma WalkTypeCount.applyStepWord_append
  {w₁ w₂ : List HStep}
  {f : YoungDiagram →₀ ℤ} :
-- imply
  WalkTypeCount.applyStepWord (w₁ ++ w₂) f = WalkTypeCount.applyStepWord w₂ (WalkTypeCount.applyStepWord w₁ f) := by
-- proof
  induction w₁ generalizing f with
  | nil => simp [WalkTypeCount.applyStepWord]
  | cons s rest ih =>
    cases s with
    | U => simp only [List.cons_append, WalkTypeCount.applyStepWord]; exact ih _
    | D => simp only [List.cons_append, WalkTypeCount.applyStepWord]; exact ih _

/--
[walkTypeCount_dnUn_eq_sum_over_partitions](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/SumSquaresFactorial.lean)
-/
@[path]
lemma walkTypeCount_dnUn_eq_sum_over_partitions
  {n : ℕ} :
-- imply
  WalkTypeCount.walkTypeCount (dnUn n) ⊥ = ∑ μ ∈ youngDiagramsOfSize n, WalkTypeCount.walkTypeCount (List.replicate n HStep.U) μ * Nat.card (HasseWalk (List.replicate n HStep.D) μ ⊥) := by
-- proof
  suffices h : (WalkTypeCount.walkTypeCount (dnUn n) ⊥ : ℤ) =
    ∑ μ ∈ youngDiagramsOfSize n,
      (WalkTypeCount.walkTypeCount (List.replicate n HStep.U) μ : ℤ) *
      (Nat.card (HasseWalk (List.replicate n HStep.D) μ ⊥) : ℤ) by
    exact_mod_cast h
  rw [WalkTypeCount.walkTypeCount_eq_applyStepWord_coeff]
  show (WalkTypeCount.applyStepWord (dnUn n) WalkCountFormula.emptyBasis) ⊥ = _
  rw [show dnUn n = List.replicate n HStep.U ++ List.replicate n HStep.D from rfl]
  rw [WalkTypeCount.applyStepWord_append]
  set g := WalkTypeCount.applyStepWord (List.replicate n HStep.U)
    WalkCountFormula.emptyBasis with g_def
  have hg : ∀ μ, g μ = (WalkTypeCount.walkTypeCount (List.replicate n HStep.U) μ : ℤ) := by
    intro μ; rw [g_def, ← WalkTypeCount.walkTypeCount_eq_applyStepWord_coeff]
  have hD : ∀ μ, (WalkTypeCount.applyStepWord (List.replicate n HStep.D)
    (Finsupp.single μ 1)) ⊥ =
    (Nat.card (HasseWalk (List.replicate n HStep.D) μ ⊥) : ℤ) := by
    intro μ; rw [← WalkTypeCount.walkTypeCount_general]
  have hg_decomp : g = g.support.sum (fun μ => Finsupp.single μ (g μ)) :=
    (Finsupp.sum_single g).symm
  have hlin : (WalkTypeCount.applyStepWord (List.replicate n HStep.D) g) ⊥ =
    ∑ μ ∈ g.support, g μ *
      (WalkTypeCount.applyStepWord (List.replicate n HStep.D) (Finsupp.single μ 1)) ⊥ := by
    conv_lhs => rw [hg_decomp]
    rw [show g.support.sum (fun μ => Finsupp.single μ (g μ)) =
      g.support.sum (fun μ => g μ • Finsupp.single μ 1) from by
      congr 1; ext μ; rw [Finsupp.smul_single', mul_one]]
    clear hg_decomp hD hg g_def
    induction g.support using Finset.cons_induction_on with
    | empty => simp [WalkTypeCount.applyStepWord_zero]
    | cons a S ha ih =>
      rw [Finset.sum_cons, WalkTypeCount.applyStepWord_add,
        WalkTypeCount.applyStepWord_smul, Finsupp.add_apply,
        Finsupp.smul_apply, smul_eq_mul, ih, Finset.sum_cons]
  rw [hlin]
  simp_rw [hg, hD]
  classical
  have hsub : g.support ⊆ youngDiagramsOfSize n := by
    intro μ hμ
    rw [Finsupp.mem_support_iff, hg] at hμ
    rw [mem_youngDiagramsOfSize]
    by_contra h; apply hμ
    simp only [Nat.cast_eq_zero]
    rw [WalkTypeCount.walkTypeCount]
    simp only [Nat.card_eq_zero]; left; constructor
    intro ⟨d, start_eq, target_eq, step_up, _⟩
    have hlen : (List.replicate n HStep.U).length = n := List.length_replicate
    have card_at : ∀ k : ℕ, (hk : k ≤ n) →
      (d ⟨k, by omega⟩).card = (⊥ : YoungDiagram).card + k := by
      intro k hk
      induction k with
      | zero => simp only [Nat.add_zero]; exact congr_arg YoungDiagram.card start_eq
      | succ k ih =>
        have hk' : k ≤ n := by omega
        have hi : (List.replicate n HStep.U)[(⟨k, by rw [hlen]; omega⟩ :
          Fin (List.replicate n HStep.U).length)] = HStep.U := by
          simp [List.getElem_replicate]
        have hcov := step_up ⟨k, by rw [hlen]; omega⟩ hi
        rw [HasseWalks.card_covBy_succ hcov, ih hk']; omega
    have h1 := card_at n le_rfl
    have h2 : d ⟨n, by omega⟩ = μ := by
      convert target_eq using 2; exact Fin.ext (by simp [hlen])
    rw [h2, HasseWalkFormula.bot_card] at h1
    exact absurd (by simpa using h1) h
  exact Finset.sum_subset hsub (fun μ _ hμ => by
    rw [Finsupp.mem_support_iff, not_not] at hμ
    rw [hg] at hμ; simp [hμ])

/--
[hasseWalkCount_allD_to_bot_eq_numSYT](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/SumSquaresFactorial.lean)
-/
@[path]
lemma hasseWalkCount_allD_to_bot_eq_numSYT
  {n : ℕ}
  {μ : YoungDiagram}
-- given
  (hμ : μ.card = n) :
-- imply
  Nat.card (HasseWalk (List.replicate n HStep.D) μ ⊥) = numSYT μ := by
-- proof
  subst hμ
  unfold HasseWalkFormula.numSYT
  apply Nat.card_congr
  have hlen : (List.replicate μ.card HStep.D).length = μ.card := List.length_replicate
  have hcast : (List.replicate μ.card HStep.D).length + 1 = μ.card + 1 := by omega
  refine {
    toFun := fun w => ?_
    invFun := fun s => ?_
    left_inv := fun w => ?_
    right_inv := fun s => ?_
  }
  ·
    refine ⟨fun i => w.diagram (Fin.cast hcast.symm ⟨μ.card - i.val, by omega⟩), ?_, ?_,
      fun i => ?_⟩
    ·
      simp only [Nat.sub_zero]
      convert w.target_eq using 2
      exact Fin.ext (by simp [Fin.cast, hlen])
    ·
      simp only [Nat.sub_self]
      convert w.start_eq using 2
    ·
      have hi_lt : μ.card - i.val - 1 < (List.replicate μ.card HStep.D).length := by
        simp only [hlen]; omega
      have hi_eq : (List.replicate μ.card HStep.D)[μ.card - i.val - 1]'hi_lt = HStep.D := by
        simp [List.getElem_replicate]
      have hsd := w.step_down ⟨μ.card - i.val - 1, hi_lt⟩ hi_eq
      convert hsd using 2
      exact Fin.ext (by dsimp [Fin.cast]; omega)
  ·
    obtain ⟨chain, hstart, htarget, hstep⟩ := s
    refine ⟨fun i => chain ⟨μ.card - (Fin.cast hcast i).val, by omega⟩, ?_, ?_,
      fun i hi_u => ?_, fun i hi_d => ?_⟩
    ·
      convert htarget using 2
    ·
      convert hstart using 2
      exact Fin.ext (by simp [Fin.cast, hlen])
    ·
      exact absurd hi_u (by simp [List.getElem_replicate])
    ·
      have hi_lt_n : μ.card - i.val - 1 < μ.card := by
        have := i.isLt; simp only [hlen] at this; omega
      have := hstep ⟨μ.card - i.val - 1, hi_lt_n⟩
      convert this using 2
      exact Fin.ext (by dsimp [Fin.cast]; omega)
  ·
    obtain ⟨d, s, t, su, sd⟩ := w
    simp only [HasseWalk.mk.injEq]
    funext ⟨i, hi⟩
    exact congr_arg d (Fin.ext (by simp [Fin.cast]; omega))
  ·
    obtain ⟨chain, h1, h2, h3⟩ := s
    exact Subtype.ext (funext fun ⟨i, hi⟩ => congr_arg chain (Fin.ext (by
      simp [Fin.cast]; omega)))

/--
[walkTypeCount_allU_eq_numSYT](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/SumSquaresFactorial.lean)
-/
@[path]
lemma walkTypeCount_allU_eq_numSYT
  {n : ℕ}
  {μ : YoungDiagram}
-- given
  (hμ : μ.card = n) :
-- imply
  WalkTypeCount.walkTypeCount (List.replicate n HStep.U) μ = numSYT μ := by
-- proof
  subst hμ
  suffices h : WalkTypeCount.walkTypeCount (List.replicate μ.card HStep.U) μ =
    HasseWalkFormula.upWalkCount μ.card μ by
    rw [h]; unfold HasseWalkFormula.upWalkCount HasseWalkFormula.numSYT; rfl
  unfold WalkTypeCount.walkTypeCount HasseWalkFormula.upWalkCount
  apply Nat.card_congr
  have hlen : (List.replicate μ.card HStep.U).length = μ.card := List.length_replicate
  refine {
    toFun := fun w => ?_
    invFun := fun s => ?_
    left_inv := fun w => ?_
    right_inv := fun s => ?_
  }
  ·
    refine ⟨fun i => w.diagram (Fin.cast (by omega) i), w.start_eq, ?_, fun i => ?_⟩
    ·
      convert w.target_eq using 2
      exact Fin.ext (by simp [hlen])
    ·
      have hi_lt : i.val < (List.replicate μ.card HStep.U).length := by omega
      have hi_eq : (List.replicate μ.card HStep.U)[i.val]'hi_lt = HStep.U := by
        simp [List.getElem_replicate]
      have := w.step_up (⟨i.val, hi_lt⟩ : Fin (List.replicate μ.card HStep.U).length) hi_eq
      convert this using 2
  ·
    obtain ⟨chain, hstart, htarget, hstep⟩ := s
    refine ⟨fun i => chain (Fin.cast (by omega) i), hstart, ?_, fun i hi_u => ?_, fun i hi_d => ?_⟩
    ·
      convert htarget using 2
      exact Fin.ext (by simp [hlen])
    ·
      have hi_lt : i.val < μ.card := by omega
      have := hstep (⟨i.val, hi_lt⟩ : Fin μ.card)
      convert this using 2
    ·
      exact absurd hi_d (by simp [List.getElem_replicate])
  ·
    obtain ⟨d, s, t, su, sd⟩ := w
    simp only [HasseWalk.mk.injEq]
    funext i; exact congr_arg d (Fin.ext rfl)
  ·
    obtain ⟨chain, h1, h2, h3⟩ := s
    exact Subtype.ext (funext fun i => congr_arg chain (Fin.ext rfl))

/--
[walkTypeCount_dnUn_eq_sum_numSYT_sq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/SumSquaresFactorial.lean)
-/
@[path]
lemma walkTypeCount_dnUn_eq_sum_numSYT_sq
  {n : ℕ} :
-- imply
  WalkTypeCount.walkTypeCount (dnUn n) ⊥ = ∑ μ ∈ youngDiagramsOfSize n, (numSYT μ) ^ 2 := by
-- proof
  rw [walkTypeCount_dnUn_eq_sum_over_partitions]
  apply Finset.sum_congr rfl
  intro μ hμ
  rw [mem_youngDiagramsOfSize] at hμ
  rw [walkTypeCount_allU_eq_numSYT n μ hμ, hasseWalkCount_allD_to_bot_eq_numSYT n μ hμ, sq]

/--
[dnUn_length](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/SumSquaresFactorial.lean)
-/
@[path]
lemma dnUn_length
  {n : ℕ} :
-- imply
  (dnUn n).length = n + n := by
-- proof
  simp [dnUn]

/--
[dnUn_getElem_U](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/SumSquaresFactorial.lean)
-/
@[path]
lemma dnUn_getElem_U
  {n : ℕ}
  {i : Fin (dnUn n).length}
-- given
  (hlt : i.val < n) :
-- imply
  (dnUn n)[i] = HStep.U := by
-- proof
  show (dnUn n)[i.val] = HStep.U
  simp only [dnUn]
  rw [List.getElem_append_left (by simp; omega)]
  simp

/--
[dnUn_getElem_D](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/SumSquaresFactorial.lean)
-/
@[path]
lemma dnUn_getElem_D
  {n : ℕ}
  {i : Fin (dnUn n).length}
-- given
  (hge : n ≤ i.val) :
-- imply
  (dnUn n)[i] = HStep.D := by
-- proof
  show (dnUn n)[i.val] = HStep.D
  simp only [dnUn]
  rw [List.getElem_append_right (by simp; omega)]
  simp

/--
[dnUn_downPositions_mem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/SumSquaresFactorial.lean)
-/
@[path]
lemma dnUn_downPositions_mem
  {n : ℕ}
  {i : Fin (dnUn n).length} :
-- imply
  i ∈ WalkTypeCount.downPositions (dnUn n) ↔ n ≤ i.val := by
-- proof
  simp only [WalkTypeCount.downPositions, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hi
    by_contra h
    have h' : i.val < n := by omega
    have hU := dnUn_getElem_U i h'
    rw [hU] at hi
    exact absurd hi (by decide)
  · intro hi
    exact dnUn_getElem_D i hi

/--
[dnUn_take](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/SumSquaresFactorial.lean)
-/
@[path]
lemma dnUn_take
  {n : ℕ}
  {i : Fin (dnUn n).length}
-- given
  (hge : n ≤ i.val) :
-- imply
  (dnUn n).take i.val = List.replicate n HStep.U ++ List.replicate (i.val - n) HStep.D := by
-- proof
  have hlen : i.val < n + n := by rw [← dnUn_length]; exact i.isLt
  simp only [dnUn]
  rw [List.take_append]
  simp only [List.length_replicate, List.take_replicate]
  congr 1
  · congr 1; omega
  · congr 1; omega

/--
[dnUn_numURight_D](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/SumSquaresFactorial.lean)
-/
@[path]
lemma dnUn_numURight_D
  {n : ℕ}
  {i : Fin (dnUn n).length}
-- given
  (hge : n ≤ i.val) :
-- imply
  WalkTypeCount.numURight (dnUn n) i = n := by
-- proof
  simp only [WalkTypeCount.numURight, dnUn_take i hge, List.filter_append,
    List.filter_replicate, List.length_append]
  simp (config := { decide := true })

/--
[dnUn_numDRight_D](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/SumSquaresFactorial.lean)
-/
@[path]
lemma dnUn_numDRight_D
  {n : ℕ}
  {i : Fin (dnUn n).length}
-- given
  (hge : n ≤ i.val) :
-- imply
  WalkTypeCount.numDRight (dnUn n) i = i.val - n := by
-- proof
  simp only [WalkTypeCount.numDRight, dnUn_take i hge, List.filter_append,
    List.filter_replicate, List.length_append]
  simp (config := { decide := true })

/--
[dnUn_downStepProduct_eq_factorial](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/SumSquaresFactorial.lean)
-/
@[path]
lemma dnUn_downStepProduct_eq_factorial
  {n : ℕ} :
-- imply
  WalkTypeCount.downStepProduct (dnUn n) = ↑(n.factorial) := by
-- proof
  unfold WalkTypeCount.downStepProduct
  suffices hfact : (↑(n.factorial) : ℤ) = ∏ i ∈ Finset.range n, (↑(n - i) : ℤ) by
    rw [hfact]
    apply Finset.prod_nbij (fun i => i.val - n)
    · intro i hi
      rw [Finset.mem_range]
      have hge := (dnUn_downPositions_mem i).mp hi
      have hlt : i.val < n + n := by rw [← dnUn_length]; exact i.isLt
      omega
    · intro a ha b hb (hab : a.val - n = b.val - n)
      have hage := (dnUn_downPositions_mem a).mp ha
      have hbge := (dnUn_downPositions_mem b).mp hb
      exact Fin.ext (by omega)
    · intro k hk
      simp only [Finset.coe_range, Set.mem_Iio] at hk
      have hkl : k + n < (dnUn n).length := by rw [dnUn_length]; omega
      exact ⟨⟨k + n, hkl⟩, (dnUn_downPositions_mem _).mpr (by simp), by simp⟩
    · intro i hi
      have hge := (dnUn_downPositions_mem i).mp hi
      rw [dnUn_numURight_D i hge, dnUn_numDRight_D i hge]
      have hlt : i.val < n + n := by rw [← dnUn_length]; exact i.isLt
      omega
  have key : ∀ m : ℕ, (↑(m.factorial) : ℤ) = ∏ i ∈ Finset.range m, (↑i + 1 : ℤ) := by
    intro m; induction m with
    | zero => simp
    | succ m ih =>
      rw [Nat.factorial_succ, Nat.cast_mul, ih, Finset.prod_range_succ]
      push_cast; ring
  rw [key n]
  apply Finset.prod_nbij (fun i => n - 1 - i)
  · intro i hi; simp at hi ⊢; omega
  · intro a ha b hb hab
    simp at ha hb
    show a = b
    have : n - 1 - a = n - 1 - b := hab
    omega
  · intro k hk
    simp at hk ⊢
    exact ⟨n - 1 - k, by omega, by omega⟩
  · intro i hi
    simp at hi
    have h : n - (n - 1 - i) = i + 1 := by omega
    rw [h]; push_cast; ring

/--
[dnUn_runningLevel_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/SumSquaresFactorial.lean)
-/
@[path]
lemma dnUn_runningLevel_le
  {n k : ℕ}
-- given
  (hk : k ≤ n) :
-- imply
  WalkTypeCount.runningLevel (dnUn n) k = (k : ℤ) := by
-- proof
  simp only [WalkTypeCount.runningLevel, dnUn]
  have htake : (List.replicate n HStep.U ++ List.replicate n HStep.D).take k =
    List.replicate k HStep.U := by
    rw [List.take_append]
    simp only [List.length_replicate, List.take_replicate]
    have h1 : min k n = k := min_eq_left hk
    have h2 : k - n = 0 := Nat.sub_eq_zero_of_le hk
    simp [h1, h2]
  rw [htake]
  simp only [List.filter_replicate]
  simp (config := { decide := true })

/--
[dnUn_runningLevel_ge](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/SumSquaresFactorial.lean)
-/
@[path]
lemma dnUn_runningLevel_ge
  {n k : ℕ}
-- given
  (hge : n ≤ k)
  (hle : k ≤ n + n) :
-- imply
  WalkTypeCount.runningLevel (dnUn n) k = (2 * n - k : ℤ) := by
-- proof
  simp only [WalkTypeCount.runningLevel, dnUn]
  have htake : (List.replicate n HStep.U ++ List.replicate n HStep.D).take k =
    List.replicate n HStep.U ++ List.replicate (k - n) HStep.D := by
    rw [List.take_append]
    simp only [List.length_replicate, List.take_replicate]
    congr 1
    · congr 1; omega
    · congr 1; omega
  rw [htake]
  simp only [List.filter_append, List.filter_replicate, List.length_append]
  simp (config := { decide := true })
  omega

/--
[isValidStepWord_dnUn](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/SumSquaresFactorial.lean)
-/
@[path]
lemma isValidStepWord_dnUn
  {n : ℕ} :
-- imply
  WalkTypeCount.IsValidStepWord (dnUn n) 0 := by
-- proof
  constructor
  ·
    have hlen : (dnUn n).length = n + n := dnUn_length n
    rw [hlen, dnUn_runningLevel_ge n (n + n) (Nat.le_add_right n n) (le_refl _)]
    push_cast; omega
  ·
    intro k hk
    have hlen : (dnUn n).length = n + n := dnUn_length n
    rw [hlen] at hk
    by_cases h : k ≤ n
    · rw [dnUn_runningLevel_le n k h]
      exact Nat.cast_nonneg k
    · rw [dnUn_runningLevel_ge n k (by omega) hk]
      omega

/--
[walkTypeCount_dnUn_bot_eq_factorial](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/SumSquaresFactorial.lean)
-/
@[path]
lemma walkTypeCount_dnUn_bot_eq_factorial
  {n : ℕ} :
-- imply
  WalkTypeCount.walkTypeCount (dnUn n) ⊥ = n.factorial := by
-- proof
  have hvalid : WalkTypeCount.IsValidStepWord (dnUn n) (⊥ : YoungDiagram).card := by
    rw [HasseWalkFormula.bot_card]; exact isValidStepWord_dnUn n
  have h83 := WalkTypeCount.walkTypeCount_eq_numSYT_mul_prod (dnUn n) ⊥ hvalid
  rw [HasseWalkFormula.numSYT_bot, dnUn_downStepProduct_eq_factorial] at h83
  simp only [Nat.cast_one, one_mul] at h83
  exact_mod_cast h83

/--
[sum_numSYT_sq_eq_factorial](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/SumSquaresFactorial.lean)
-/
@[path]
lemma sum_numSYT_sq_eq_factorial
  {n : ℕ} :
-- imply
  ∑ μ ∈ youngDiagramsOfSize n, (numSYT μ) ^ 2 = n.factorial := by
-- proof
  have h1 := walkTypeCount_dnUn_eq_sum_numSYT_sq n
  have h2 := walkTypeCount_dnUn_bot_eq_factorial n
  omega

/--
[finite_youngDiagrams_of_size](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/SumSquaresFactorial.lean)
-/
@[path]
private lemma finite_youngDiagrams_of_size_eq
  {n : ℕ} :
-- imply
  Set.Finite {μ : YoungDiagram | μ.card = n} := by
-- proof
  apply finite_youngDiagrams_of_size n


-- created on 2026-10-23
