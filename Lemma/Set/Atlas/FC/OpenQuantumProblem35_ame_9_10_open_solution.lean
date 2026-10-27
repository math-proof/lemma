import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.FC.OpenQuantumProblem35_ame_9_10_open_solution.Part8
open OpenQuantumProblem35
open scoped BigOperators


namespace OpenQuantumProblem35

/--
[detFinThreeInt_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean)
-/
@[path]
lemma detFinThreeInt_eq
  {M : Matrix (Fin 3) (Fin 3) ℤ} :
-- imply
  M.det = detFinThreeInt M := by
-- proof
  rw [Matrix.det_fin_three]
  simp [detFinThreeInt]
  ring

end OpenQuantumProblem35

namespace OpenQuantumProblem35

/--
[detFinFourInt_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean)
-/
@[path]
lemma detFinFourInt_eq
  {M : Matrix (Fin 4) (Fin 4) ℤ} :
-- imply
  M.det = detFinFourInt M := by
-- proof
  rw [Matrix.det_succ_row M 0]
  apply Finset.sum_congr rfl
  intro j hj
  rw [detFinThreeInt_eq]
  simp [detFinFourInt]

end OpenQuantumProblem35

namespace OpenQuantumProblem35

/--
[detFinFiveInt_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean)
-/
@[path]
lemma detFinFiveInt_eq
  {M : Matrix (Fin 5) (Fin 5) ℤ} :
-- imply
  M.det = detFinFiveInt M := by
-- proof
  rw [Matrix.det_succ_row M 0]
  apply Finset.sum_congr rfl
  intro j hj
  rw [detFinFourInt_eq]
  simp [detFinFiveInt]

end OpenQuantumProblem35

namespace OpenQuantumProblem35

/--
[q5Indices_mem_sort](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean)
-/
@[path]
lemma q5Indices_mem_sort
  {A : Finset (Fin 10)} :
-- imply
  q5Indices (fun i => decide (i ∈ A)) true = A.sort (· ≤ ·) := by
-- proof
  apply List.SortedLT.eq_of_mem_iff
  · exact ((List.sortedLT_finRange 10).pairwise.filter _).sortedLT
  · exact Finset.sortedLT_sort A
  · intro i
    simp [q5Indices]

end OpenQuantumProblem35

namespace OpenQuantumProblem35

/--
[q5Indices_not_sort](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean)
-/
@[path]
lemma q5Indices_not_sort
  {A : Finset (Fin 10)} :
-- imply
  q5Indices (fun i => decide (i ∈ A)) false = Aᶜ.sort (· ≤ ·) := by
-- proof
  apply List.SortedLT.eq_of_mem_iff
  · exact ((List.sortedLT_finRange 10).pairwise.filter _).sortedLT
  · exact Finset.sortedLT_sort Aᶜ
  · intro i
    simp [q5Indices]

end OpenQuantumProblem35

namespace OpenQuantumProblem35

/--
[q5Select_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean)
-/
@[path]
lemma q5Select_mem
  {A : Finset (Fin 10)}
  {k : Fin 5}
-- given
  (hA : A.card = 5) :
-- imply
  q5Select (fun i => decide (i ∈ A)) true k = ((A.orderIsoOfFin hA) k).1.1 := by
-- proof
  simp only [q5Select, q5Indices_mem_sort A]
  rw [List.getElem?_eq_getElem (by simpa [hA] using k.2)]
  rfl
set_option maxHeartbeats 0 in

end OpenQuantumProblem35

namespace OpenQuantumProblem35

/--
[q5Select_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean)
-/
@[path]
lemma q5Select_not_mem
  {A : Finset (Fin 10)}
  {k : Fin 5}
-- given
  (hA : A.card = 5) :
-- imply
  q5Select (fun i => decide (i ∈ A)) false k = ((Aᶜ.orderIsoOfFin (by simp [Finset.card_compl, hA])) k).1.1 := by
-- proof
  simp only [q5Select, q5Indices_not_sort A]
  have hc : Aᶜ.card = 5 := by simp [Finset.card_compl, hA]
  rw [List.getElem?_eq_getElem (by simpa [hc] using k.2)]
  rfl

end OpenQuantumProblem35

namespace OpenQuantumProblem35

/--
[q5Graph_affine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean)
-/
@[path]
lemma q5Graph_affine
  {s : Fin 10}
  {flip : Bool}
  {i j : Fin 10} :
-- imply
  q5Graph (q5Affine s flip i) (q5Affine s flip j) = q5Graph i j := by
-- proof
  decide +revert

end OpenQuantumProblem35

namespace OpenQuantumProblem35

/--
[q5Representatives_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean)
-/
@[path]
lemma q5Representatives_card
  {R : Finset (Fin 10)}
-- given
  (hR : R ∈ q5Representatives) :
-- imply
  R.card = 5 := by
-- proof
  simp only [q5Representatives, List.mem_cons, List.not_mem_nil, or_false] at hR
  obtain (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | := hR
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> decide

end OpenQuantumProblem35

namespace OpenQuantumProblem35

/--
[q5Cut_classification](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean)
-/
@[path]
lemma q5Cut_classification
  {A : Finset (Fin 10)}
-- given
  (hA : A.card = 5) :
-- imply
  ∃ R ∈ q5Representatives, ∃ s : Fin 10, ∃ flip : Bool, A = R.map (q5Affine s flip).toEmbedding := by
-- proof
  set_option maxRecDepth 10000 in
    revert A
    exact of_decide_eq_true rfl

end OpenQuantumProblem35

namespace OpenQuantumProblem35

/--
[q5Representative_certificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean)
-/
@[path]
lemma q5Representative_certificate
-- imply
  ∀ R : Finset (Fin 10), R ∈ q5Representatives → detFinFiveInt (q5MaskMatrix (fun i => decide (i ∈ R))) % 5 ≠ 0 := by
-- proof
  intro R hR
  simp only [q5Representatives, List.mem_cons, List.not_mem_nil, or_false] at hR
  obtain (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | := hR
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  all_goals exact of_decide_eq_true rfl

end OpenQuantumProblem35

namespace OpenQuantumProblem35

/--
[q5CutMatrix_det_of_certificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean)
-/
@[path]
lemma q5CutMatrix_det_of_certificate
  {A : Finset (Fin 10)}
-- given
  (hA : A.card = 5)
  (hcert : detFinFiveInt (q5MaskMatrix (fun i => decide (i ∈ A))) % 5 ≠ 0) :
-- imply
  (q5CutMatrix A hA).det ≠ 0 := by
-- proof
  let mask : Fin 10 → Bool := fun i => decide (i ∈ A)
  let M : Matrix (Fin 5) (Fin 5) ℤ := q5MaskMatrix mask
  have hmap : (Int.castRingHom (ZMod 5)).mapMatrix M = q5CutMatrix A hA := by
    funext i j
    change ((q5GraphNat (q5Select (fun i => decide (i ∈ A)) false i)
      (q5Select (fun i => decide (i ∈ A)) true j) : ℤ) : ZMod 5) = _
    rw [q5Select_not_mem A hA i, q5Select_mem A hA j]
    simp [q5CutMatrix, q5GraphNat, q5Graph]
  intro hz
  have hz' : ((M.det : ℤ) : ZMod 5) = 0 := by
    calc
      ((M.det : ℤ) : ZMod 5) =
        ((Int.castRingHom (ZMod 5)).mapMatrix M).det := Int.cast_det M
      _ = (q5CutMatrix A hA).det := congrArg Matrix.det hmap
      _ = 0 := hz
  have hdvd : (5 : ℤ) ∣ M.det :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (M.det) 5).mp hz'
  apply hcert
  change detFinFiveInt M % 5 = 0
  rw [← detFinFiveInt_eq M]
  exact Int.emod_eq_zero_of_dvd hdvd

end OpenQuantumProblem35

namespace OpenQuantumProblem35

/--
[q5CutMatrix_det_map](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean)
-/
@[path]
lemma q5CutMatrix_det_map
  {A : Finset (Fin 10)}
  {g : Equiv.Perm (Fin 10)}
-- given
  (hA : A.card = 5)
  (hg : ∀ i j, q5Graph (g i) (g j) = q5Graph i j)
  (hd : (q5CutMatrix A hA).det ≠ 0) :
-- imply
  (q5CutMatrix (A.map g.toEmbedding) (by simpa using hA)).det ≠ 0 := by
-- proof
  let B := A.map g.toEmbedding
  let hB : B.card = 5 := by simpa [B] using hA
  let hAc : Aᶜ.card = 5 := by simp [Finset.card_compl, hA]
  let hBc : Bᶜ.card = 5 := by simp [Finset.card_compl, hB]
  let eA := A.orderIsoOfFin hA
  let eB := B.orderIsoOfFin hB
  let eC := Aᶜ.orderIsoOfFin hAc
  let eD := Bᶜ.orderIsoOfFin hBc
  let pA : Equiv.Perm (Fin 5) :=
    eA.toEquiv.trans ((finsetMapEquiv g A).trans eB.toEquiv.symm)
  let pC : Equiv.Perm (Fin 5) :=
    eC.toEquiv.trans ((finsetMapComplEquiv g A).trans eD.toEquiv.symm)
  have hmat : q5CutMatrix A hA =
    (q5CutMatrix B hB).submatrix pC pA := by
    ext i j
    unfold q5CutMatrix
    dsimp only [Matrix.submatrix_apply]
    have hpA : (eB (pA j)).1 = g (eA j).1 := by
      change (eB (eB.symm ((finsetMapEquiv g A) (eA j)))).1 =
        ((finsetMapEquiv g A) (eA j)).1
      exact congrArg Subtype.val (eB.apply_symm_apply ((finsetMapEquiv g A) (eA j)))
    have hpC : (eD (pC i)).1 = g (eC i).1 := by
      change (eD (eD.symm ((finsetMapComplEquiv g A) (eC i)))).1 =
        ((finsetMapComplEquiv g A) (eC i)).1
      exact congrArg Subtype.val (eD.apply_symm_apply ((finsetMapComplEquiv g A) (eC i)))
    rw [hpA, hpC]
    exact (hg _ _).symm
  intro hz
  have hzB : (q5CutMatrix B hB).det = 0 := by
    simpa [B] using hz
  apply hd
  rw [hmat]
  have hdet := Matrix.det_reindex pC.symm pA.symm (q5CutMatrix B hB)
  rw [Matrix.reindex_apply] at hdet
  simpa [hzB] using hdet

end OpenQuantumProblem35

namespace OpenQuantumProblem35

/--
[q5CutMatrix_det](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean)
-/
@[path]
lemma q5CutMatrix_det
  {A : Finset (Fin 10)}
-- given
  (hA : A.card = 5) :
-- imply
  (q5CutMatrix A hA).det ≠ 0 := by
-- proof
  obtain ⟨R, hR, s, flip, rfl⟩ := q5Cut_classification A hA
  have hRc := q5Representatives_card R hR
  apply q5CutMatrix_det_map R hRc (q5Affine s flip) (q5Graph_affine s flip)
  exact q5CutMatrix_det_of_certificate R hRc (q5Representative_certificate R hR)

end OpenQuantumProblem35

namespace OpenQuantumProblem35

/--
[q5Graph_cut_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean)
-/
@[path]
lemma q5Graph_cut_injective
  {A : Finset (Fin 10)}
-- given
  (hA : A.card = 5) :
-- imply
  Function.Injective (fun x : A → ZMod 5 => fun j : {j : Fin 10 // j ∉ A} => ∑ i : A, q5Graph j.1 i.1 * x i) := by
-- proof
  intro x y hxy
  let hAc : Aᶜ.card = 5 := by simp [Finset.card_compl, hA]
  let eA := A.orderIsoOfFin hA
  let eC := Aᶜ.orderIsoOfFin hAc
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hd : IsUnit (q5CutMatrix A hA).det :=
    (isUnit_iff_ne_zero).2 (q5CutMatrix_det A hA)
  have hu : IsUnit (q5CutMatrix A hA) :=
    (Matrix.isUnit_iff_isUnit_det _).2 hd
  have hvout : (q5CutMatrix A hA).mulVec (x ∘ eA) =
    (q5CutMatrix A hA).mulVec (y ∘ eA) := by
    funext r
    have her : (eC r).1 ∉ A := by
      simpa only [Finset.mem_compl] using (eC r).2
    have hr := congrFun hxy ⟨(eC r).1, her⟩
    change (∑ j : Fin 5, q5Graph (eC r).1 (eA j).1 * x (eA j)) =
      ∑ j : Fin 5, q5Graph (eC r).1 (eA j).1 * y (eA j)
    calc
      _ = ∑ i : A, q5Graph (eC r).1 i.1 * x i :=
        eA.toEquiv.sum_comp (fun i : A => q5Graph (eC r).1 i.1 * x i)
      _ = ∑ i : A, q5Graph (eC r).1 i.1 * y i := hr
      _ = _ := (eA.toEquiv.sum_comp
        (fun i : A => q5Graph (eC r).1 i.1 * y i)).symm
  have hv := Matrix.mulVec_injective_of_isUnit hu hvout
  funext i
  obtain ⟨r, rfl⟩ := eA.surjective i
  exact congrFun hv r

end OpenQuantumProblem35

namespace OpenQuantumProblem35

/--
[q2Cycle_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean)
-/
@[path]
lemma q2Cycle_symm
  {i j : Fin 9} :
-- imply
  q2Cycle i j = q2Cycle j i := by
-- proof
  simp only [q2Cycle, Nat.dist_comm]

end OpenQuantumProblem35

namespace OpenQuantumProblem35

/--
[q2Cycle_diag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean)
-/
@[path]
lemma q2Cycle_diag
  {i : Fin 9} :
-- imply
  q2Cycle i i = 0 := by
-- proof
  simp [q2Cycle]

end OpenQuantumProblem35

namespace OpenQuantumProblem35

/--
[q5Graph_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean)
-/
@[path]
lemma q5Graph_symm
  {i j : Fin 10} :
-- imply
  q5Graph i j = q5Graph j i := by
-- proof
  simp only [q5Graph, Nat.dist_comm]

end OpenQuantumProblem35

namespace OpenQuantumProblem35

/--
[q5Graph_diag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean)
-/
@[path]
lemma q5Graph_diag
  {i : Fin 10} :
-- imply
  q5Graph i i = 0 := by
-- proof
  simp [q5Graph]

end OpenQuantumProblem35

namespace OpenQuantumProblem35

/--
[graph_cross_generic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean)
-/
@[path]
lemma graph_cross_generic
  {n p : ℕ}
  {G : Fin n → Fin n → ZMod p}
  {x d : Fin n → ZMod p}
-- given
  (hsym : ∀ i j, G i j = G j i)
  (hdiag : ∀ i, G i i = 0) :
-- imply
  (∑ i, ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.1 < j.1), G i j * (x i * d j + d i * x j)) = ∑ i, x i * ∑ j, G i j * d j := by
-- proof
  calc
    _ = ∑ i, ∑ j ∈ Finset.Ioi i,
      ((x i * G i j * d j) + (x j * G j i * d i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr
      · ext j
        simp
      · intro j hj
        rw [← hsym i j]
        ring
    _ = ∑ i, ∑ j ∈ ({i}ᶜ : Finset (Fin n)), x i * G i j * d j :=
      Finset.sum_sum_Ioi_add_eq_sum_sum_off_diag _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      have he : Finset.univ.erase i = ({i}ᶜ : Finset (Fin n)) := by
        ext j
        simp [eq_comm]
      have hs := Finset.sum_erase_add Finset.univ
        (fun j => x i * (G i j * d j)) (Finset.mem_univ i)
      rw [he] at hs
      rw [← hs]
      simp [hdiag]
      apply Finset.sum_congr rfl
      intro j hj
      ring

end OpenQuantumProblem35

namespace OpenQuantumProblem35

/--
[q2Cycle_cross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean)
-/
@[path]
lemma q2Cycle_cross
  {x d : Fin 9 → ZMod 2} :
-- imply
  (∑ i, ∑ j ∈ Finset.univ.filter (fun j : Fin 9 => i.1 < j.1), q2Cycle i j * (x i * d j + d i * x j)) = ∑ i, x i * ∑ j, q2Cycle i j * d j :=
-- proof
  graph_cross_generic q2Cycle q2Cycle_symm q2Cycle_diag x d

end OpenQuantumProblem35

namespace OpenQuantumProblem35

/--
[q5Graph_cross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean)
-/
@[path]
lemma q5Graph_cross
  {x d : Fin 10 → ZMod 5} :
-- imply
  (∑ i, ∑ j ∈ Finset.univ.filter (fun j : Fin 10 => i.1 < j.1), q5Graph i j * (x i * d j + d i * x j)) = ∑ i, x i * ∑ j, q5Graph i j * d j :=
-- proof
  graph_cross_generic q5Graph q5Graph_symm q5Graph_diag x d

end OpenQuantumProblem35

namespace OpenQuantumProblem35

/--
[q2Cycle_subgroup_minWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean)
-/
@[path]
lemma q2Cycle_subgroup_minWeight
  {x : Fin 9 → ZMod 2}
-- given
  (h0 : q2Check₁ x = 0)
  (h1 : q2Check₂ x = 0)
  (hx : x ≠ 0) :
-- imply
  5 ≤ (Finset.univ.filter fun i => x i ≠ 0 ∨ (∑ j, q2Cycle i j * x j) ≠ 0).card := by
-- proof
  set_option maxRecDepth 10000 in
    decide +revert

end OpenQuantumProblem35

namespace OpenQuantumProblem35

/--
[sum_stdAddChar_dot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean)
-/
@[path]
lemma sum_stdAddChar_dot
  {N : ℕ}
  [NeZero N]
  [Fintype ι]
  [DecidableEq ι]
  {c : ι → ZMod N} :
-- imply
  (∑ z : ι → ZMod N, ZMod.stdAddChar (∑ i, c i * z i)) = if c = 0 then (N ^ Fintype.card ι : ℂ) else 0 := by
-- proof
  have h1 (t : ZMod N) : (∑ a : ZMod N, ZMod.stdAddChar (t * a)) =
    if t = 0 then (N : ℂ) else 0 := by
    split_ifs with h
    · simp [h, ZMod.card]
    · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar N h)
  have hmap' (s : Finset ι) (z : ι → ZMod N) :
    ZMod.stdAddChar (∑ i ∈ s, c i * z i) =
      ∏ i ∈ s, ZMod.stdAddChar (c i * z i) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih => simp [ha, AddChar.map_add_eq_mul, ih]
  have hmap (z : ι → ZMod N) :
    ZMod.stdAddChar (∑ i, c i * z i) =
      ∏ i, ZMod.stdAddChar (c i * z i) := by
    simpa using hmap' Finset.univ z
  calc
    _ = ∑ z : ι → ZMod N, ∏ i, ZMod.stdAddChar (c i * z i) := by
      simp_rw [hmap]
    _ = ∏ i, ∑ a : ZMod N, ZMod.stdAddChar (c i * a) :=
      (@Fintype.prod_sum ι ℂ _ _ _ (fun _ => ZMod N) _
        (fun i a => ZMod.stdAddChar (c i * a))).symm
    _ = _ := by
      simp_rw [h1]
      split_ifs with h
      · subst c
        simp [ZMod.card]
      · have hi : ∃ i, c i ≠ 0 := by
        simpa [funext_iff] using h
        obtain ⟨i, hi⟩ := hi
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        simp [hi]

end OpenQuantumProblem35

namespace OpenQuantumProblem35

/--
[stdAddChar_mul_star](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean)
-/
@[path]
lemma stdAddChar_mul_star
  {N : ℕ}
  [NeZero N]
  {a b : ZMod N} :
-- imply
  ZMod.stdAddChar a * star (ZMod.stdAddChar b) = ZMod.stdAddChar (a - b) := by
-- proof
  change ZMod.stdAddChar a * (starRingEnd ℂ) (ZMod.stdAddChar b) = _
  rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul, sub_eq_add_neg]

end OpenQuantumProblem35

namespace OpenQuantumProblem35

/--
[norm_stdAddChar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean)
-/
@[path]
lemma norm_stdAddChar
  {N : ℕ}
  [NeZero N]
  {a : ZMod N} :
-- imply
  ‖ZMod.stdAddChar a‖ = 1 := by
-- proof
  rw [ZMod.stdAddChar_apply]
  exact Circle.norm_coe _

end OpenQuantumProblem35

namespace OpenQuantumProblem35

/--
[graphPhase_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean)
-/
@[path]
lemma graphPhase_add
  {n p : ℕ}
  {G : Fin n → Fin n → ZMod p}
  {x d : Fin n → ZMod p} :
-- imply
  graphPhase G (x + d) = graphPhase G x + graphPhase G d + ∑ i, ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.1 < j.1), G i j * (x i * d j + d i * x j) := by
-- proof
  simp only [graphPhase, Pi.add_apply]
  simp_rw [mul_add, add_mul, Finset.sum_add_distrib]
  ring

end OpenQuantumProblem35

namespace OpenQuantumProblem35

/--
[q2Phase_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean)
-/
@[path]
lemma q2Phase_sub
  {x y : Fin 9 → ZMod 2} :
-- imply
  graphPhase q2Cycle x - graphPhase q2Cycle y = graphPhase q2Cycle (x - y) + ∑ i, y i * ∑ j, q2Cycle i j * (x j - y j) := by
-- proof
  have h := graphPhase_add q2Cycle y (x - y)
  rw [show y + (x - y) = x by abel] at h
  rw [h, q2Cycle_cross]
  simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  ring

end OpenQuantumProblem35

namespace OpenQuantumProblem35

/--
[q5Phase_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean)
-/
@[path]
lemma q5Phase_sub
  {x y : Fin 10 → ZMod 5} :
-- imply
  graphPhase q5Graph x - graphPhase q5Graph y = graphPhase q5Graph (x - y) + ∑ i, y i * ∑ j, q5Graph i j * (x j - y j) := by
-- proof
  have h := graphPhase_add q5Graph y (x - y)
  rw [show y + (x - y) = x by abel] at h
  rw [h, q5Graph_cross]
  simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  ring

end OpenQuantumProblem35

namespace OpenQuantumProblem35

/--
[sum_stdAddChar_affine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean)
-/
@[path]
lemma sum_stdAddChar_affine
  {N : ℕ}
  [NeZero N]
  [Fintype ι]
  [DecidableEq ι]
  {b : ZMod N}
  {c : ι → ZMod N} :
-- imply
  (∑ z : ι → ZMod N, ZMod.stdAddChar (b + ∑ i, c i * z i)) = ZMod.stdAddChar b * (if c = 0 then (N ^ Fintype.card ι : ℂ) else 0) := by
-- proof
  simp_rw [AddChar.map_add_eq_mul, ← Finset.mul_sum]
  rw [sum_stdAddChar_dot]

end OpenQuantumProblem35

namespace OpenQuantumProblem35

/--
[q2Label_dot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean)
-/
@[path]
lemma q2Label_dot
  {a : Fin 2 → ZMod 2}
  {x : Fin 9 → ZMod 2} :
-- imply
  (∑ i, q2Label a i * x i) = a 0 * q2Check₁ x + a 1 * q2Check₂ x := by
-- proof
  decide +revert

end OpenQuantumProblem35

namespace OpenQuantumProblem35

/--
[q5Graph_zero_of_supported](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean)
-/
@[path]
lemma q5Graph_zero_of_supported
  {A : Finset (Fin 10)}
  {d : Fin 10 → ZMod 5}
-- given
  (hA : A.card = 5)
  (hsupp : ∀ i, i ∉ A → d i = 0)
  (hcoeff : ∀ j, j ∉ A → (∑ i, q5Graph j i * d i) = 0) :
-- imply
  d = 0 := by
-- proof
  have hxy : (fun j : {j : Fin 10 // j ∉ A} =>
    ∑ i : A, q5Graph j.1 i.1 * d i.1) =
    (fun _ : {j : Fin 10 // j ∉ A} => 0) := by
    funext j
    rw [← hcoeff j.1 j.2]
    calc
      (∑ i : A, q5Graph j.1 i.1 * d i.1) =
        ∑ i ∈ A, q5Graph j.1 i * d i := by
          simpa only [] using
            (Finset.sum_coe_sort A (fun i : Fin 10 => q5Graph j.1 i * d i))
      _ = ∑ i, q5Graph j.1 i * d i := by
        apply Finset.sum_subset (Finset.subset_univ A)
        intro i _ hi
        rw [hsupp i hi, mul_zero]
  have hdA : (fun i : A => d i.1) = 0 := by
    apply q5Graph_cut_injective A hA
    simpa using hxy
  funext i
  by_cases hi : i ∈ A
  · exact congrFun hdA ⟨i, hi⟩
  · exact hsupp i hi

end OpenQuantumProblem35

namespace OpenQuantumProblem35

/--
[q2Cycle_zero_of_small_supported](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean)
-/
@[path]
lemma q2Cycle_zero_of_small_supported
  {A : Finset (Fin 9)}
  {d : Fin 9 → ZMod 2}
-- given
  (hA : A.card ≤ 4)
  (hsupp : ∀ i, i ∉ A → d i = 0)
  (hcoeff : ∀ j, j ∉ A → (∑ i, q2Cycle j i * d i) = 0)
  (h0 : q2Check₁ d = 0)
  (h1 : q2Check₂ d = 0) :
-- imply
  d = 0 := by
-- proof
  by_contra hd
  have hw := q2Cycle_subgroup_minWeight d h1 h2 hd
  let B := Finset.univ.filter fun i =>
    d i ≠ 0 ∨ (∑ j, q2Cycle i j * d j) ≠ 0
  have hBA : B ⊆ A := by
    intro i hi
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    by_contra hn
    exact hi.elim (fun h => h (hsupp i hn)) (fun h => h (hcoeff i hn))
  change 5 ≤ B.card at hw
  have hcard : B.card ≤ A.card := Finset.card_le_card hBA
  omega
set_option maxHeartbeats 0

end OpenQuantumProblem35

namespace OpenQuantumProblem35

/--
[q2_phase_paste_affine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean)
-/
@[path]
lemma q2_phase_paste_affine
  {A : Finset (Fin 9)}
  {a : Fin 2 → ZMod 2}
  {x y : A → ZMod 2}
-- given
  (z : {i : Fin 9 // i ∉ A} → ZMod 2) :
-- imply
  let d := pasteOn A x 0 - pasteOn A y 0 binaryPhase a (pasteOn A x z) - binaryPhase a (pasteOn A y z) = (graphPhase q2Cycle d + ∑ i ∈ A.attach, y i * ∑ j, q2Cycle i.1 j * d j + ∑ i, q2Label a i * d i) + ∑ i : {i : Fin 9 // i ∉ A}, z i * (∑ j, q2Cycle i.1 j * d j) := by
-- proof
  dsimp only
  have hd : pasteOn A x z - pasteOn A y z =
    pasteOn A x 0 - pasteOn A y 0 := by
    funext i
    by_cases hi : i ∈ A <;> simp [pasteOn, hi]
  have hg := q2Phase_sub (pasteOn A x z) (pasteOn A y z)
  simp only [binaryPhase]
  rw [show
    (graphPhase q2Cycle (pasteOn A x z) +
      ∑ i, q2Label a i * pasteOn A x z i) -
      (graphPhase q2Cycle (pasteOn A y z) +
        ∑ i, q2Label a i * pasteOn A y z i) =
      (graphPhase q2Cycle (pasteOn A x z) -
        graphPhase q2Cycle (pasteOn A y z)) +
      ((∑ i, q2Label a i * pasteOn A x z i) -
        ∑ i, q2Label a i * pasteOn A y z i) by ring]
  rw [hg, hd]
  simp only [Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← mul_sub]
  have hdj (j : Fin 9) : pasteOn A x z j - pasteOn A y z j =
    (pasteOn A x 0 - pasteOn A y 0) j := congrFun hd j
  simp_rw [hdj]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun i : Fin 9 => i ∈ A)
    (fun i => pasteOn A y z i *
      ∑ j, q2Cycle i j * (pasteOn A x 0 - pasteOn A y 0) j)]
  simp only [pasteOn_mem, pasteOn_not_mem]
  rw [add_assoc]
  have hu : (@Finset.univ {i : Fin 9 // i ∈ A} (Subtype.fintype _)) =
    (@Finset.univ (↥A) (Finset.Subtype.fintype A)) := by
    ext i
    simp
  rw [hu]
  rw [Finset.sum_coe_sort_eq_attach A]
  ring

end OpenQuantumProblem35

namespace OpenQuantumProblem35

/--
[sum_binary_labels](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean)
-/
@[path]
lemma sum_binary_labels
  {b : ZMod 2}
  {d : Fin 9 → ZMod 2} :
-- imply
  (∑ a : Fin 2 → ZMod 2, ZMod.stdAddChar (b + ∑ i, q2Label a i * d i)) = if q2Check₁ d = 0 ∧ q2Check₂ d = 0 then (4 : ℂ) * ZMod.stdAddChar b else 0 := by
-- proof
  let c : Fin 2 → ZMod 2 := ![q2Check₁ d, q2Check₂ d]
  have hdot (a : Fin 2 → ZMod 2) :
    (∑ i, q2Label a i * d i) = ∑ k, c k * a k := by
    rw [q2Label_dot]
    simp only [c, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.tail_cons]
    ring
  simp_rw [hdot]
  rw [sum_stdAddChar_affine]
  have hc : c = 0 ↔ q2Check₁ d = 0 ∧ q2Check₂ d = 0 := by
    constructor
    · intro h
      exact ⟨congrFun h 0, congrFun h 1⟩
    · rintro ⟨h1, h2⟩
      funext i
      fin_cases i <;> simp [c, h1, h2]
  by_cases h : c = 0
  · have hh := hc.mp h
    simp [h, hh]
    ring
  · have hh : ¬(q2Check₁ d = 0 ∧ q2Check₂ d = 0) := fun hh => h (hc.mpr hh)
    simp [h, hh]

end OpenQuantumProblem35

namespace OpenQuantumProblem35

/--
[q2_phase_paste_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean)
-/
@[path]
lemma q2_phase_paste_sum
  {A : Finset (Fin 9)}
  {x y : A → ZMod 2}
-- given
  (hA : A.card = 4) :
-- imply
  (∑ a : Fin 2 → ZMod 2, ∑ z : {i : Fin 9 // i ∉ A} → ZMod 2, ZMod.stdAddChar (binaryPhase a (pasteOn A x z)) * star (ZMod.stdAddChar (binaryPhase a (pasteOn A y z)))) = if x = y then (2 ^ 7 : ℂ) else 0 := by
-- proof
  let d : Fin 9 → ZMod 2 := pasteOn A x 0 - pasteOn A y 0
  let c : {i : Fin 9 // i ∉ A} → ZMod 2 :=
    fun i => ∑ j, q2Cycle i.1 j * d j
  let b : ZMod 2 := graphPhase q2Cycle d +
    ∑ i ∈ A.attach, y i * ∑ j, q2Cycle i.1 j * d j
  have hform (a : Fin 2 → ZMod 2) (z : {i : Fin 9 // i ∉ A} → ZMod 2) :
    binaryPhase a (pasteOn A x z) - binaryPhase a (pasteOn A y z) =
      (b + ∑ i, q2Label a i * d i) + ∑ i, c i * z i := by
    rw [q2_phase_paste_affine]
    dsimp [b, c, d]
    congr 2
    funext i
    ac_rfl
  simp_rw [stdAddChar_mul_star, hform, sum_stdAddChar_affine]
  have hcard : Fintype.card {i : Fin 9 // i ∉ A} = 5 := by
    rw [Fintype.card_subtype_compl (fun i : Fin 9 => i ∈ A)]
    simpa [hA] using (show Fintype.card (Fin 9) - A.card = 5 by simp [hA])
  by_cases hc : c = 0
  · rw [if_pos hc]
    simp only [hcard]
    rw [← Finset.sum_mul, sum_binary_labels]
    by_cases hh : q2Check₁ d = 0 ∧ q2Check₂ d = 0
    · have hd : d = 0 := by
      apply q2Cycle_zero_of_small_supported A (by omega)
      · intro i hi
        simp [d, pasteOn, hi]
      · intro i hi
        exact congrFun hc ⟨i, hi⟩
      · exact hh.1
      · exact hh.2
      have hxy : x = y := by
        funext i
        have hi := congrFun hd i.1
        exact sub_eq_zero.mp (by simpa [d, pasteOn, i.2] using hi)
      subst y
      have hh0 : q2Check₁ (0 : Fin 9 → ZMod 2) = 0 ∧
        q2Check₂ (0 : Fin 9 → ZMod 2) = 0 := by
        simp [q2Check₁, q2Check₂]
      simp [hd, b, hh0, graphPhase]
      norm_num
    · have hxy : x ≠ y := by
      intro hxy
      subst y
      apply hh
      constructor <;> simp [d, q2Check₁, q2Check₂]
      simp [hh, hxy]
  · have hxy : x ≠ y := by
    intro hxy
    subst y
    apply hc
    funext i
    simp [c, d]
    simp [hc, hxy]

end OpenQuantumProblem35

namespace OpenQuantumProblem35

/--
[q5Logical_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean)
-/
@[path]
lemma q5Logical_injective
-- imply
  Function.Injective q5Logical := by
-- proof
  decide +revert

end OpenQuantumProblem35

namespace OpenQuantumProblem35

/--
[quinary_phase_physical_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean)
-/
@[path]
lemma quinary_phase_physical_sum
  {A : Finset (Fin 9)}
  {a b : Fin 2 → ZMod 2}
  {x y : A → ZMod 5}
-- given
  (hA : A.card = 4) :
-- imply
  (∑ z : {i : Fin 9 // i ∉ A} → ZMod 5, ZMod.stdAddChar (quinaryPhase a (pasteOn A x z)) * star (ZMod.stdAddChar (quinaryPhase b (pasteOn A y z)))) = if a = b ∧ x = y then (5 ^ 5 : ℂ) else 0 := by
-- proof
  let d : Fin 10 → ZMod 5 :=
    quinaryWord a (pasteOn A x 0) - quinaryWord b (pasteOn A y 0)
  let c : {i : Fin 9 // i ∉ A} → ZMod 5 :=
    fun i => ∑ j, q5Graph (Fin.succ i.1) j * d j
  let e : ZMod 5 := graphPhase q5Graph d +
    q5Logical b * (∑ j, q5Graph 0 j * d j) +
    ∑ i ∈ A.attach, y i * ∑ j, q5Graph (Fin.succ i.1) j * d j
  have hd (z : {i : Fin 9 // i ∉ A} → ZMod 5) :
    quinaryWord a (pasteOn A x z) - quinaryWord b (pasteOn A y z) = d := by
    funext i
    refine Fin.cases ?_ (fun k => ?_) i
    · simp [d]
    · by_cases hk : k ∈ A <;> simp [d, pasteOn, hk]
  have hform (z : {i : Fin 9 // i ∉ A} → ZMod 5) :
    quinaryPhase a (pasteOn A x z) - quinaryPhase b (pasteOn A y z) =
      e + ∑ i, c i * z i := by
    unfold quinaryPhase
    rw [q5Phase_sub]
    have hdj (j : Fin 10) :
      quinaryWord a (pasteOn A x z) j - quinaryWord b (pasteOn A y z) j = d j :=
      congrFun (hd z) j
    simp_rw [hdj]
    have hsplit :
      (∑ i : Fin 10, quinaryWord b (pasteOn A y z) i *
        ∑ j, q5Graph i j * d j) =
      q5Logical b * (∑ j, q5Graph 0 j * d j) +
        ∑ i : Fin 9, pasteOn A y z i *
          ∑ j, q5Graph (Fin.succ i) j * d j := by
      rw [Fin.sum_univ_succ]
      simp only [quinaryWord_zero, quinaryWord_succ]
    rw [hsplit]
    have hparts :
      (∑ i : Fin 9, pasteOn A y z i *
        ∑ j, q5Graph (Fin.succ i) j * d j) =
      (∑ i ∈ A.attach, y i * ∑ j, q5Graph (Fin.succ i.1) j * d j) +
        ∑ i : {i : Fin 9 // i ∉ A}, z i *
          ∑ j, q5Graph (Fin.succ i.1) j * d j := by
      rw [← Fintype.sum_subtype_add_sum_subtype (fun i : Fin 9 => i ∈ A)]
      simp only [pasteOn_mem, pasteOn_not_mem]
      have hu : (@Finset.univ {i : Fin 9 // i ∈ A} (Subtype.fintype _)) =
        (@Finset.univ (↥A) (Finset.Subtype.fintype A)) := by
        ext i
        simp
      rw [hu, Finset.sum_coe_sort_eq_attach A]
    have hg := congrArg (graphPhase q5Graph) (hd z)
    rw [hg]
    rw [hparts]
    dsimp only [e, c]
    have ht :
      (∑ i : {i : Fin 9 // i ∉ A}, z i *
        ∑ j, q5Graph (Fin.succ i.1) j * d j) =
      ∑ i : {i : Fin 9 // i ∉ A},
        (∑ j, q5Graph (Fin.succ i.1) j * d j) * z i := by
      apply Finset.sum_congr rfl
      intro i hi
      ac_rfl
    rw [ht]
    ring
  simp_rw [stdAddChar_mul_star, hform, sum_stdAddChar_affine]
  have hcard : Fintype.card {i : Fin 9 // i ∉ A} = 5 := by
    rw [Fintype.card_subtype_compl (fun i : Fin 9 => i ∈ A)]
    simpa [hA] using (show Fintype.card (Fin 9) - A.card = 5 by simp [hA])
  have hc : c = 0 ↔ a = b ∧ x = y := by
    constructor
    · intro hc0
      have hd0 : d = 0 := by
        apply q5Graph_zero_of_supported (liftPhysicalSet A) (by simp [hA])
        · intro i hi
          have hi0 : i ≠ 0 := by
            intro hiEq
            subst i
            exact hi (liftPhysicalSet_zero A)
          obtain ⟨k, rfl⟩ := Fin.eq_succ_of_ne_zero hi0
          have hk : k ∉ A := by simpa using hi
          simp [d, pasteOn, hk]
        · intro i hi
          have hi0 : i ≠ 0 := by
            intro hiEq
            subst i
            exact hi (liftPhysicalSet_zero A)
          obtain ⟨k, rfl⟩ := Fin.eq_succ_of_ne_zero hi0
          have hk : k ∉ A := by simpa using hi
          exact congrFun hc0 ⟨k, hk⟩
      constructor
      · apply q5Logical_injective
        have hz := congrFun hd0 0
        exact sub_eq_zero.mp (by simpa [d] using hz)
      · funext i
        have hi := congrFun hd0 (Fin.succ i.1)
        exact sub_eq_zero.mp (by simpa [d, pasteOn, i.2] using hi)
    · rintro ⟨rfl, rfl⟩
      funext i
      simp [c, d]
  by_cases h : a = b ∧ x = y
  · have hc0 := hc.mpr h
    rw [if_pos hc0, if_pos h]
    simp only [hcard]
    obtain ⟨rfl, rfl⟩ := h
    have hd0 : d = 0 := by
      funext i
      simp [d]
    simp [hd0, e, graphPhase]
  · have hc0 : c ≠ 0 := fun hc0 => h (hc.mp hc0)
    simp [hc0, h]

end OpenQuantumProblem35

namespace OpenQuantumProblem35

/--
[q5_phase_paste_affine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean)
-/
@[path]
lemma q5_phase_paste_affine
  {A : Finset (Fin 10)}
  {x y : A → ZMod 5}
-- given
  (z : {i : Fin 10 // i ∉ A} → ZMod 5) :
-- imply
  let d := pasteOn A x 0 - pasteOn A y 0 graphPhase q5Graph (pasteOn A x z) - graphPhase q5Graph (pasteOn A y z) = (graphPhase q5Graph d + ∑ i ∈ A.attach, y i * ∑ j, q5Graph i.1 j * d j) + ∑ i : {i : Fin 10 // i ∉ A}, z i * (∑ j, q5Graph i.1 j * d j) := by
-- proof
  dsimp only
  have hd : pasteOn A x z - pasteOn A y z =
    pasteOn A x 0 - pasteOn A y 0 := by
    funext i
    by_cases hi : i ∈ A
    · simp [pasteOn, hi]
    · simp [pasteOn, hi]
  rw [q5Phase_sub, hd]
  have hdj (j : Fin 10) : pasteOn A x z j - pasteOn A y z j =
    (pasteOn A x 0 - pasteOn A y 0) j := congrFun hd j
  simp_rw [hdj]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun i : Fin 10 => i ∈ A)
    (fun i => pasteOn A y z i *
      ∑ j, q5Graph i j * (pasteOn A x 0 - pasteOn A y 0) j)]
  simp only [pasteOn_mem, pasteOn_not_mem]
  rw [add_assoc]
  congr 2
  have hu : (@Finset.univ {i : Fin 10 // i ∈ A} (Subtype.fintype _)) =
    (@Finset.univ (↥A) (Finset.Subtype.fintype A)) := by
    ext i
    simp
  rw [hu]
  exact (Finset.sum_coe_sort_eq_attach A
    (fun i : A => y i * ∑ j, q5Graph i.1 j *
      (pasteOn A x 0 - pasteOn A y 0) j))

end OpenQuantumProblem35

namespace OpenQuantumProblem35

/--
[q5_phase_paste_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean)
-/
@[path]
lemma q5_phase_paste_sum
  {A : Finset (Fin 10)}
  {x y : A → ZMod 5}
-- given
  (hA : A.card = 5) :
-- imply
  (∑ z : {i : Fin 10 // i ∉ A} → ZMod 5, ZMod.stdAddChar (graphPhase q5Graph (pasteOn A x z)) * star (ZMod.stdAddChar (graphPhase q5Graph (pasteOn A y z)))) = if x = y then (5 ^ 5 : ℂ) else 0 := by
-- proof
  let d : Fin 10 → ZMod 5 := pasteOn A x 0 - pasteOn A y 0
  let c : {i : Fin 10 // i ∉ A} → ZMod 5 :=
    fun i => ∑ j, q5Graph i.1 j * d j
  let b : ZMod 5 := graphPhase q5Graph d +
    ∑ i ∈ A.attach, y i * ∑ j, q5Graph i.1 j * d j
  have hform (z : {i : Fin 10 // i ∉ A} → ZMod 5) :
    graphPhase q5Graph (pasteOn A x z) - graphPhase q5Graph (pasteOn A y z) =
      b + ∑ i, c i * z i := by
    rw [q5_phase_paste_affine]
    dsimp [b, c, d]
    congr 2
    funext i
    ac_rfl
  simp_rw [stdAddChar_mul_star, hform]
  rw [sum_stdAddChar_affine]
  have hc : c = 0 ↔ x = y := by
    constructor
    · intro hc
      have hd : d = 0 := by
        apply q5Graph_zero_of_supported A hA
        · intro i hi
          simp [d, pasteOn, hi]
        · intro i hi
          exact congrFun hc ⟨i, hi⟩
      funext i
      have hi := congrFun hd i.1
      exact sub_eq_zero.mp (by simpa [d, pasteOn, i.2] using hi)
    · intro hxy
      subst y
      funext i
      simp [c, d]
  by_cases hxy : x = y
  · subst y
    have hcard : Fintype.card {i : Fin 10 // i ∉ A} = 5 := by
      rw [Fintype.card_subtype_compl (fun i : Fin 10 => i ∈ A)]
      simpa [hA] using (show Fintype.card (Fin 10) - A.card = 5 by simp [hA])
    have hczero : c = 0 := hc.mpr rfl
    rw [if_pos hczero]
    simp [d, b, graphPhase, hcard]
  · have hc0 : c ≠ 0 := fun hc0 => hxy (hc.mp hc0)
    simp [hc0, hxy]

end OpenQuantumProblem35

namespace OpenQuantumProblem35

/--
[ameAmplitude_paste_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean)
-/
@[path]
lemma ameAmplitude_paste_split
  {A : Finset (Fin 9)}
  {x : A → Fin 10}
-- given
  (u : {i : Fin 9 // i ∉ A} → ZMod 2)
  (v : {i : Fin 9 // i ∉ A} → ZMod 5) :
-- imply
  ameAmplitude (pasteOn A x ((splitFunctionsEquiv {i : Fin 9 // i ∉ A}).symm (u, v))) = ((Real.sqrt (2 ^ 11 * 5 ^ 9 : ℝ) : ℂ)⁻¹) * ∑ a : Fin 2 → ZMod 2, ZMod.stdAddChar (binaryPhase a (pasteOn A (fun i => bitPart (x i)) u)) * ZMod.stdAddChar (quinaryPhase a (pasteOn A (fun i => quintPart (x i)) v)) := by
-- proof
  unfold ameAmplitude
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  congr 2
  · congr 1
    funext i
    by_cases hi : i ∈ A <;> simp [pasteOn, splitFunctionsEquiv, hi]
  · congr 1
    funext i
    by_cases hi : i ∈ A <;> simp [pasteOn, splitFunctionsEquiv, hi]

end OpenQuantumProblem35

namespace OpenQuantumProblem35

/--
[sum_four_comm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean)
-/
@[path]
lemma sum_four_comm
  [AddCommMonoid R]
  [Fintype U]
  [Fintype V]
  [Fintype A]
  [Fintype B]
  {f : U → V → A → B → R} :
-- imply
  (∑ u, ∑ v, ∑ a, ∑ b, f u v a b) = ∑ a, ∑ b, ∑ u, ∑ v, f u v a b := by
-- proof
  calc
    _ = ∑ u, ∑ a, ∑ v, ∑ b, f u v a b := by
      apply Finset.sum_congr rfl; intro u hu; rw [Finset.sum_comm]
    _ = ∑ a, ∑ u, ∑ v, ∑ b, f u v a b := by rw [Finset.sum_comm]
    _ = ∑ a, ∑ u, ∑ b, ∑ v, f u v a b := by
      apply Finset.sum_congr rfl; intro a ha
      apply Finset.sum_congr rfl; intro u hu
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl; intro a ha; rw [Finset.sum_comm]

end OpenQuantumProblem35

namespace OpenQuantumProblem35

/--
[sum_separable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean)
-/
@[path]
lemma sum_separable
  [CommRing R]
  [Fintype U]
  [Fintype V]
  {K : R}
  {B : U → R}
  {Q : V → R} :
-- imply
  (∑ u, ∑ v, K * B u * Q v) = K * (∑ u, B u) * (∑ v, Q v) := by
-- proof
  rw [Finset.mul_sum, Finset.sum_comm]
  apply Finset.sum_congr rfl; intro v hv
  rw [Finset.mul_sum, Finset.sum_mul]

end OpenQuantumProblem35

namespace OpenQuantumProblem35

/--
[sum_product_separable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean)
-/
@[path]
lemma sum_product_separable
  [CommRing R]
  [Fintype U]
  [Fintype V]
  [Fintype A]
  [Fintype B]
  {C D : R}
  {bx : A → U → R}
  {byy : B → U → R}
  {qx : A → V → R}
  {qy : B → V → R} :
-- imply
  (∑ u, ∑ v, (C * ∑ a, bx a u * qx a v) * (D * ∑ b, byy b u * qy b v)) = C * D * ∑ a, ∑ b, (∑ u, bx a u * byy b u) * (∑ v, qx a v * qy b v) := by
-- proof
  calc
    _ = ∑ u, ∑ v, ∑ a, ∑ b,
      C * D * (bx a u * byy b u) * (qx a v * qy b v) := by
      apply Finset.sum_congr rfl; intro u hu
      apply Finset.sum_congr rfl; intro v hv
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro a ha
      apply Finset.sum_congr rfl; intro b hb
      ring
    _ = ∑ a, ∑ b, ∑ u, ∑ v,
      C * D * (bx a u * byy b u) * (qx a v * qy b v) :=
      sum_four_comm _
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro a ha
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro b hb
      rw [show C * D * ((∑ u, bx a u * byy b u) *
        (∑ v, qx a v * qy b v)) =
        C * D * (∑ u, bx a u * byy b u) *
        (∑ v, qx a v * qy b v) by ring]
      exact sum_separable (C * D) _ _

end OpenQuantumProblem35

namespace OpenQuantumProblem35

/--
[ameAmplitude_paste_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean)
-/
@[path]
lemma ameAmplitude_paste_sum
  {A : Finset (Fin 9)}
  {x y : A → Fin 10}
-- given
  (hA : A.card = 4) :
-- imply
  (∑ z : {i : Fin 9 // i ∉ A} → Fin 10, ameAmplitude (pasteOn A x z) * star (ameAmplitude (pasteOn A y z))) = if x = y then ((10 ^ 4 : ℂ)⁻¹) else 0 := by
-- proof
  let xb : A → ZMod 2 := fun i => bitPart (x i)
  let yb : A → ZMod 2 := fun i => bitPart (y i)
  let xq : A → ZMod 5 := fun i => quintPart (x i)
  let yq : A → ZMod 5 := fun i => quintPart (y i)
  let C : ℂ := (Real.sqrt (2 ^ 11 * 5 ^ 9 : ℝ) : ℂ)⁻¹
  have hparts : x = y ↔ xb = yb ∧ xq = yq := by
    constructor
    · rintro rfl
      exact ⟨rfl, rfl⟩
    · rintro ⟨hb, hq⟩
      funext i
      apply localPartsEquiv.injective
      rw [localPartsEquiv_apply, localPartsEquiv_apply]
      exact Prod.ext (congrFun hb i) (congrFun hq i)
  rw [← (splitFunctionsEquiv {i : Fin 9 // i ∉ A}).symm.sum_comp]
  rw [Fintype.sum_prod_type]
  simp_rw [ameAmplitude_paste_split]
  change (∑ u, ∑ v,
    (C * ∑ a, ZMod.stdAddChar (binaryPhase a (pasteOn A xb u)) *
      ZMod.stdAddChar (quinaryPhase a (pasteOn A xq v))) *
      (starRingEnd ℂ) (C * ∑ b,
        ZMod.stdAddChar (binaryPhase b (pasteOn A yb u)) *
        ZMod.stdAddChar (quinaryPhase b (pasteOn A yq v)))) = _
  simp_rw [map_mul, map_sum]
  have hstar (b : Fin 2 → ZMod 2)
    (u : {i : Fin 9 // i ∉ A} → ZMod 2)
    (v : {i : Fin 9 // i ∉ A} → ZMod 5) :
    (starRingEnd ℂ)
      (ZMod.stdAddChar (binaryPhase b (pasteOn A yb u)) *
        ZMod.stdAddChar (quinaryPhase b (pasteOn A yq v))) =
      (starRingEnd ℂ) (ZMod.stdAddChar (binaryPhase b (pasteOn A yb u))) *
        (starRingEnd ℂ) (ZMod.stdAddChar (quinaryPhase b (pasteOn A yq v))) := by
    exact map_mul (starRingEnd ℂ) _ _
  simp_rw [hstar]
  rw [sum_product_separable]
  have hqsum (a b : Fin 2 → ZMod 2) :
    (∑ v : {i : Fin 9 // i ∉ A} → ZMod 5,
      ZMod.stdAddChar (quinaryPhase a (pasteOn A xq v)) *
        (starRingEnd ℂ) (ZMod.stdAddChar (quinaryPhase b (pasteOn A yq v)))) =
      if a = b ∧ xq = yq then (5 ^ 5 : ℂ) else 0 :=
    quinary_phase_physical_sum A hA a b xq yq
  simp_rw [hqsum]
  by_cases hq : xq = yq
  · have hx_iff : x = y ↔ xb = yb := by simpa [hq] using hparts
    simp only [hq, and_true]
    simp_rw [mul_ite]
    simp only [mul_zero, Fintype.sum_ite_eq]
    rw [← Finset.sum_mul]
    have hbsum :
      (∑ a : Fin 2 → ZMod 2,
        ∑ u : {i : Fin 9 // i ∉ A} → ZMod 2,
          ZMod.stdAddChar (binaryPhase a (pasteOn A xb u)) *
            (starRingEnd ℂ) (ZMod.stdAddChar
              (binaryPhase a (pasteOn A yb u)))) =
        if xb = yb then (2 ^ 7 : ℂ) else 0 :=
      q2_phase_paste_sum A hA xb yb
    rw [hbsum]
    by_cases hb : xb = yb
    · rw [if_pos hb, if_pos (hx_iff.mpr hb)]
      dsimp [C]
      norm_num [map_inv₀]
      have hs : Real.sqrt (4000000000 : ℝ) ^ 2 = 4000000000 :=
        Real.sq_sqrt (by norm_num)
      have hnR : Real.sqrt (4000000000 : ℝ) ≠ 0 := by positivity
      have hn : (Real.sqrt (4000000000 : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast hnR
      field_simp
      exact_mod_cast hs.symm
    · rw [if_neg hb, if_neg (fun h => hb (hx_iff.mp h))]
      ring
  · have hxy : x ≠ y := fun h => hq (hparts.mp h).2
    simp [hq, hxy]

end OpenQuantumProblem35

namespace OpenQuantumProblem35

/--
[ameState_norm_sq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean)
-/
@[path]
lemma ameState_norm_sq_sum
-- imply
  (∑ w : Config 9 10, ‖ameAmplitude w‖ ^ 2) = 1 := by
-- proof
  let A : Finset (Fin 9) := Finset.univ.filter (fun i => i.1 < 4)
  have hA : A.card = 4 := by decide
  apply Complex.ofReal_injective
  push_cast
  rw [← (splitOnEquiv (R := Fin 10) A).sum_comp]
  rw [Fintype.sum_prod_type]
  have hn (z : ℂ) : (↑‖z‖ : ℂ) ^ 2 = z * star z := by
    exact (RCLike.mul_conj z).symm
  simp_rw [hn]
  change (∑ x : A → Fin 10, ∑ z : {i : Fin 9 // i ∉ A} → Fin 10,
    ameAmplitude (pasteOn A x z) * star (ameAmplitude (pasteOn A x z))) = 1
  have hc (x : A → Fin 10) :
    (∑ z : {i : Fin 9 // i ∉ A} → Fin 10,
      ameAmplitude (pasteOn A x z) * star (ameAmplitude (pasteOn A x z))) =
      ((10 ^ 4 : ℂ)⁻¹) := by
    simpa [splitOnEquiv] using ameAmplitude_paste_sum A hA x x
  simp_rw [hc]
  simp [Fintype.card_fun, Fintype.card_coe, hA]
  norm_num

end OpenQuantumProblem35

namespace OpenQuantumProblem35

/--
[ameState_normalized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean)
-/
@[path]
lemma ameState_normalized
-- imply
  IsNormalized ameState := by
-- proof
  rw [IsNormalized, EuclideanSpace.norm_eq]
  change Real.sqrt (∑ w : Config 9 10, ‖ameAmplitude w‖ ^ 2) = 1
  rw [ameState_norm_sq_sum]
  norm_num

end OpenQuantumProblem35

namespace OpenQuantumProblem35

/--
[permFirstSet_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean)
-/
@[path]
lemma permFirstSet_card
  {π : Equiv.Perm (Fin 9)} :
-- imply
  (permFirstSet π).card = 4 := by
-- proof
  rw [← Fintype.card_coe]
  rw [Fintype.card_congr (permFrontEquiv π)]
  simp

end OpenQuantumProblem35

namespace OpenQuantumProblem35

/--
[permuteConfig_combineFirst_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean)
-/
@[path]
lemma permuteConfig_combineFirst_four
  {π : Equiv.Perm (Fin 9)}
  {x : Config 4 10}
  {z : Config 5 10} :
-- imply
  permuteConfig π (combineFirst 4 (by omega) x z) = pasteOn (permFirstSet π) (fun i => x (permFrontEquiv π i)) (fun i => z (permRestEquiv π i)) := by
-- proof
  funext i
  by_cases hi : i ∈ permFirstSet π
  · simp only [permuteConfig, combineFirst, pasteOn, hi, ↓reduceDIte]
    rw [dif_pos ((permFirstSet_mem π i).mp hi)]
    rfl
  · simp only [permuteConfig, combineFirst, pasteOn, hi, ↓reduceDIte]
    have hn : ¬(π i).1 < 4 := by simpa using hi
    rw [dif_neg hn]
    rfl

end OpenQuantumProblem35

namespace OpenQuantumProblem35

/--
[ameState_reduction_permuted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean)
-/
@[path]
lemma ameState_reduction_permuted
  {π : Equiv.Perm (Fin 9)} :
-- imply
  HasMaximallyMixedFirstReduction (n := 9) (d := 10) (9 / 2) (Nat.div_le_self 9 2) (permuteState π ameState) := by
-- proof
  unfold HasMaximallyMixedFirstReduction
  ext x y
  change (∑ z : Config 5 10,
    ameAmplitude (permuteConfig π (combineFirst 4 (by omega) x z)) *
      star (ameAmplitude (permuteConfig π (combineFirst 4 (by omega) y z)))) = _
  simp_rw [permuteConfig_combineFirst_four]
  let A := permFirstSet π
  let xb : A → Fin 10 := fun i => x (permFrontEquiv π i)
  let yb : A → Fin 10 := fun i => y (permFrontEquiv π i)
  let e : Config 5 10 ≃ ({i : Fin 9 // i ∉ A} → Fin 10) :=
    Equiv.arrowCongr (permRestEquiv π).symm (Equiv.refl (Fin 10))
  change (∑ z : Config 5 10,
    ameAmplitude (pasteOn A xb (e z)) * star (ameAmplitude (pasteOn A yb (e z)))) = _
  calc
    _ = ∑ z : {i : Fin 9 // i ∉ A} → Fin 10,
      ameAmplitude (pasteOn A xb z) * star (ameAmplitude (pasteOn A yb z)) :=
      e.sum_comp (fun z =>
        ameAmplitude (pasteOn A xb z) * star (ameAmplitude (pasteOn A yb z)))
    _ = if xb = yb then ((10 ^ 4 : ℂ)⁻¹) else 0 :=
      ameAmplitude_paste_sum A (permFirstSet_card π) xb yb
    _ = _ := by
      have hxy : xb = yb ↔ x = y := by
        constructor
        · intro h
          funext k
          obtain ⟨i, rfl⟩ := (permFrontEquiv π).surjective k
          exact congrFun h i
        · rintro rfl
          rfl
      simp only [hxy]
      by_cases h : x = y
      · subst y
        simp [maximallyMixed, Fintype.card_fun]
        norm_num
      · simp [maximallyMixed, Fintype.card_fun, h]

end OpenQuantumProblem35

namespace OpenQuantumProblem35

/--
[ame_9_10_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean)
-/
@[path]
lemma ame_9_10_open
-- imply
  ame_9_10_open_statement := by
-- proof
  unfold ame_9_10_open_statement ExistsAME IsAME
  exact ⟨ameState, ameState_normalized, ameState_reduction_permuted⟩

end OpenQuantumProblem35

/--
[localPartsEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean)
-/
@[path]
private lemma localPartsEquiv_apply_eq
  {x : Fin 10} :
-- imply
  localPartsEquiv x = (bitPart x, quintPart x) := by
-- proof
  apply OpenQuantumProblem35.localPartsEquiv_apply x

/--
[quinaryWord_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean)
-/
@[path]
private lemma quinaryWord_zero_eq
  {a : Fin 2 → ZMod 2}
  {v : Fin 9 → ZMod 5} :
-- imply
  quinaryWord a v 0 = q5Logical a := by
-- proof
  apply OpenQuantumProblem35.quinaryWord_zero a v

/--
[quinaryWord_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean)
-/
@[path]
private lemma quinaryWord_succ_eq
  {a : Fin 2 → ZMod 2}
  {v : Fin 9 → ZMod 5}
  {i : Fin 9} :
-- imply
  quinaryWord a v (Fin.succ i) = v i := by
-- proof
  apply OpenQuantumProblem35.quinaryWord_succ a v i

/--
[pasteOn_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean)
-/
@[path]
private lemma pasteOn_mem_eq
  [DecidableEq ι]
  {A : Finset ι}
  {x : A → R}
  {i : A}
-- given
  (z : {i : ι // i ∉ A} → R) :
-- imply
  pasteOn A x z i.1 = x i := by
-- proof
  apply OpenQuantumProblem35.pasteOn_mem A x z i

/--
[pasteOn_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean)
-/
@[path]
private lemma pasteOn_not_mem_eq
  [DecidableEq ι]
  {A : Finset ι}
  {x : A → R}
-- given
  (z : {i : ι // i ∉ A} → R)
  (i : {i : ι // i ∉ A}) :
-- imply
  pasteOn A x z i.1 = z i := by
-- proof
  apply OpenQuantumProblem35.pasteOn_not_mem A x z i

/--
[liftPhysicalSet_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean)
-/
@[path]
private lemma liftPhysicalSet_card_eq
  {A : Finset (Fin 9)} :
-- imply
  (liftPhysicalSet A).card = A.card + 1 := by
-- proof
  apply OpenQuantumProblem35.liftPhysicalSet_card A

/--
[liftPhysicalSet_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean)
-/
@[path]
private lemma liftPhysicalSet_zero_eq
  {A : Finset (Fin 9)} :
-- imply
  (0 : Fin 10) ∈ liftPhysicalSet A := by
-- proof
  apply OpenQuantumProblem35.liftPhysicalSet_zero A

/--
[liftPhysicalSet_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean)
-/
@[path]
private lemma liftPhysicalSet_succ_eq
  {A : Finset (Fin 9)}
  {i : Fin 9} :
-- imply
  Fin.succ i ∈ liftPhysicalSet A ↔ i ∈ A := by
-- proof
  apply OpenQuantumProblem35.liftPhysicalSet_succ A i

/--
[bitPart_localPartsEquiv_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean)
-/
@[path]
private lemma bitPart_localPartsEquiv_symm_eq
  {u : ZMod 2}
  {v : ZMod 5} :
-- imply
  bitPart (localPartsEquiv.symm (u, v)) = u := by
-- proof
  apply OpenQuantumProblem35.bitPart_localPartsEquiv_symm u v

/--
[quintPart_localPartsEquiv_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean)
-/
@[path]
private lemma quintPart_localPartsEquiv_symm_eq
  {u : ZMod 2}
  {v : ZMod 5} :
-- imply
  quintPart (localPartsEquiv.symm (u, v)) = v := by
-- proof
  apply OpenQuantumProblem35.quintPart_localPartsEquiv_symm u v

/--
[permFirstSet_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean)
-/
@[path]
private lemma permFirstSet_mem_eq
  {π : Equiv.Perm (Fin 9)}
  {i : Fin 9} :
-- imply
  i ∈ permFirstSet π ↔ (π i).1 < 4 := by
-- proof
  apply OpenQuantumProblem35.permFirstSet_mem π i


-- created on 2026-10-23
