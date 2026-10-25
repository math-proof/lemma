/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MinimalPermutationsEnumeration.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.Fin.Rev
import Mathlib.Order.Fin.Basic
import Def.Combinatorics.Enumerative.MinimalPermutationsEnumeration.Part5


section

namespace MetaMathlibExt

theorem exclA_card (d : ℕ) (a : Fin (d + 1)) (hpos : 0 < a.val) :
    (exclA d a hpos).card = d + 2 - a.val := by
  let t1 : Fin (d + 2) := ⟨d + 2 - a.val, by have ha := a.isLt; omega⟩
  have htop : topSmall d a hpos = Finset.Ici t1 := rfl
  have hIio_card : (Finset.Iio t1).card = d + 2 - a.val := by
    simp only [Fin.card_Iio]
    rfl
  have himg : exclA d a hpos =
      Finset.image (fun m : Fin (d + 2) => insert m (topSmall d a hpos))
        (Finset.Iio t1) := by
    ext L
    simp only [exclA, Finset.mem_filter, Finset.mem_powersetCard,
      Finset.mem_image, Finset.mem_Iio]
    constructor
    · intro h
      obtain ⟨⟨hsub, hcard⟩, htopsub⟩ := h
      have hsdiff : ((L \ topSmall d a hpos).card) = 1 := by
        have h1 := topSmall_card d a hpos
        have h2 := Finset.card_sdiff_of_subset htopsub
        omega
      obtain ⟨m, hm⟩ := Finset.card_eq_one.mp hsdiff
      have hmem : m ∈ L ∧ m ∉ topSmall d a hpos := by
        have hmem' : m ∈ L \ topSmall d a hpos := by
          rw [hm]
          exact Finset.mem_singleton_self m
        exact Finset.mem_sdiff.mp hmem'
      have hlt : m < t1 := by
        have hni : m ∉ Finset.Ici t1 := by
          rw [← htop]
          exact hmem.2
        simp only [Finset.mem_Ici, not_le] at hni
        exact hni
      have heq : L = insert m (topSmall d a hpos) := by
        ext x
        simp only [Finset.mem_insert]
        constructor
        · intro hx
          by_cases hx2 : x ∈ topSmall d a hpos
          · exact Or.inr hx2
          · have hx3 : x ∈ L \ topSmall d a hpos :=
              Finset.mem_sdiff.mpr ⟨hx, hx2⟩
            rw [hm] at hx3
            have := Finset.mem_singleton.mp hx3
            exact Or.inl this
        · intro hx
          rcases hx with rfl | hx2
          · exact hmem.1
          · exact htopsub hx2
      exact ⟨m, hlt, heq.symm⟩
    · intro h
      obtain ⟨m, hlt, rfl⟩ := h
      have hni : m ∉ topSmall d a hpos := by
        rw [htop]
        simp only [Finset.mem_Ici, not_le]
        exact hlt
      have hcard : (insert m (topSmall d a hpos)).card = a.val + 1 := by
        rw [Finset.card_insert_of_notMem hni, topSmall_card d a hpos]
      have hsub : insert m (topSmall d a hpos) ⊆ Finset.univ :=
        Finset.subset_univ _
      exact ⟨⟨hsub, hcard⟩, Finset.subset_insert m _⟩
  rw [himg]
  have hinj : Set.InjOn (fun m : Fin (d + 2) => insert m (topSmall d a hpos))
      (Finset.Iio t1) := by
    intro m1 hm1 m2 hm2 h
    have h1 : m1 ∉ topSmall d a hpos := by
      rw [htop]
      simp only [Finset.mem_Ici, not_le]
      exact Finset.mem_Iio.mp hm1
    have h' : insert m1 (topSmall d a hpos) = insert m2 (topSmall d a hpos) := h
    have hmem : m1 ∈ insert m2 (topSmall d a hpos) := by
      rw [← h']
      exact Finset.mem_insert_self m1 _
    rcases Finset.mem_insert.mp hmem with rfl | hmem2
    · rfl
    · exact absurd hmem2 h1
  have hcard := Finset.card_image_of_injOn hinj
  rw [hcard, hIio_card]

theorem exclInter_card (d : ℕ) (a : Fin (d + 1)) (hpos : 0 < a.val) :
    (exclA d a hpos ∩ exclB d a).card = 2 := by
  have hsub := topSmall_subset_topLarge d a hpos
  have hsdiff : ((topLarge d a \ topSmall d a hpos).card) = 2 := by
    have h1 := topLarge_card d a
    have h2 := topSmall_card d a hpos
    have h3 := Finset.card_sdiff_of_subset hsub
    omega
  have himg : exclA d a hpos ∩ exclB d a =
      Finset.image (fun x : Fin (d + 2) => insert x (topSmall d a hpos))
        (topLarge d a \ topSmall d a hpos) := by
    ext L
    simp only [Finset.mem_inter, exclA, exclB, Finset.mem_filter,
      Finset.mem_powersetCard, Finset.mem_image, Finset.mem_sdiff]
    constructor
    · intro h
      obtain ⟨⟨⟨hsub, hcard⟩, hsmall⟩, ⟨⟨_, _⟩, hlarge⟩⟩ := h
      have hsdiff2 : ((L \ topSmall d a hpos).card) = 1 := by
        have h1 := topSmall_card d a hpos
        have h2 := Finset.card_sdiff_of_subset hsmall
        omega
      obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hsdiff2
      have hmem : x ∈ L ∧ x ∉ topSmall d a hpos := by
        have hmem' : x ∈ L \ topSmall d a hpos := by
          rw [hx]
          exact Finset.mem_singleton_self x
        exact Finset.mem_sdiff.mp hmem'
      have hxlarge : x ∈ topLarge d a := hlarge hmem.1
      have heq : L = insert x (topSmall d a hpos) := by
        ext y
        simp only [Finset.mem_insert]
        constructor
        · intro hy
          by_cases hy2 : y ∈ topSmall d a hpos
          · exact Or.inr hy2
          · have hy3 : y ∈ L \ topSmall d a hpos :=
              Finset.mem_sdiff.mpr ⟨hy, hy2⟩
            rw [hx] at hy3
            have := Finset.mem_singleton.mp hy3
            exact Or.inl this
        · intro hy
          rcases hy with rfl | hy2
          · exact hmem.1
          · exact hsmall hy2
      exact ⟨x, ⟨hxlarge, hmem.2⟩, heq.symm⟩
    · intro h
      obtain ⟨x, ⟨hxlarge, hsmall2⟩, rfl⟩ := h
      have hni : x ∉ topSmall d a hpos := hsmall2
      have hcard : (insert x (topSmall d a hpos)).card = a.val + 1 := by
        rw [Finset.card_insert_of_notMem hni, topSmall_card d a hpos]
      have hsub : insert x (topSmall d a hpos) ⊆ Finset.univ :=
        Finset.subset_univ _
      have hsmall : topSmall d a hpos ⊆ insert x (topSmall d a hpos) :=
        Finset.subset_insert x _
      have hlarge : insert x (topSmall d a hpos) ⊆ topLarge d a := by
        intro y hy
        simp only [Finset.mem_insert] at hy
        rcases hy with rfl | hy2
        · exact hxlarge
        · exact topSmall_subset_topLarge d a hpos hy2
      exact ⟨⟨⟨hsub, hcard⟩, hsmall⟩, ⟨⟨hsub, hcard⟩, hlarge⟩⟩
  rw [himg]
  have hinj : Set.InjOn (fun x : Fin (d + 2) => insert x (topSmall d a hpos))
      (↑(topLarge d a \ topSmall d a hpos) : Set (Fin (d + 2))) := by
    intro x1 hx1 x2 hx2 h
    have hx1' : x1 ∈ topLarge d a \ topSmall d a hpos :=
      Finset.mem_coe.mp hx1
    have h1 : x1 ∉ topSmall d a hpos := (Finset.mem_sdiff.mp hx1').2
    have h' : insert x1 (topSmall d a hpos) = insert x2 (topSmall d a hpos) := h
    have hmem : x1 ∈ insert x2 (topSmall d a hpos) := by
      rw [← h']
      exact Finset.mem_insert_self x1 _
    rcases Finset.mem_insert.mp hmem with rfl | hmem2
    · rfl
    · exact absurd hmem2 h1
  have hcard := Finset.card_image_of_injOn hinj
  rw [hcard, hsdiff]

theorem exclUnion_card (d : ℕ) (a : Fin (d + 1)) (hpos : 0 < a.val) :
    (exclA d a hpos ∪ exclB d a).card = d + 2 := by
  have hA := exclA_card d a hpos
  have hB := exclB_card d a
  have hI := exclInter_card d a hpos
  have hunion := Finset.card_union_add_card_inter (exclA d a hpos) (exclB d a)
  have ha := a.isLt
  omega

theorem vals_disjoint_union (d : ℕ) (σ : Equiv.Perm (Fin (d + 2)))
    (a : Fin (d + 1)) :
    Disjoint (firstVals d σ a) (secondVals d σ a) ∧
      firstVals d σ a ∪ secondVals d σ a = Finset.univ := by
  have hdisj : Disjoint (firstVals d σ a) (secondVals d σ a) := by
    rw [Finset.disjoint_left]
    intro y hy1 hy2
    obtain ⟨i1, _, rfl⟩ := Finset.mem_image.mp hy1
    obtain ⟨i2, _, heq2⟩ := Finset.mem_image.mp hy2
    have heq := σ.injective heq2.symm
    have hv := congrArg Fin.val heq
    simp only [block1Pos_val, block2Pos_val] at hv
    have hi1 := i1.isLt
    have hi2 := i2.isLt
    have ha := a.isLt
    omega
  have hunion : firstVals d σ a ∪ secondVals d σ a = Finset.univ := by
    ext y
    simp only [Finset.mem_union, Finset.mem_univ, iff_true]
    have hj : ∃ j : Fin (d + 2), σ j = y := ⟨σ.symm y, by simp⟩
    obtain ⟨j, rfl⟩ := hj
    by_cases hle : j.val ≤ a.val
    · have hlt : j.val < a.val + 1 := by omega
      let i : Fin (a.val + 1) := ⟨j.val, hlt⟩
      have heq : block1Pos d a i = j := by
        apply Fin.ext
        simp only [block1Pos_val]
        rfl
      exact Or.inl (by
        simp only [firstVals, Finset.mem_image, Finset.mem_univ, true_and]
        exact ⟨i, by rw [heq]⟩)
    · have hgt : a.val < j.val := by omega
      have hle2 : a.val + 1 ≤ j.val := by omega
      have hlt2 : j.val - (a.val + 1) < (d - a.val) + 1 := by
        have hj2 := j.isLt
        have ha2 := a.isLt
        omega
      let i : Fin ((d - a.val) + 1) := ⟨j.val - (a.val + 1), hlt2⟩
      have heq : block2Pos d a i = j := by
        apply Fin.ext
        simp only [block2Pos_val]
        have hi : i.val = j.val - (a.val + 1) := rfl
        omega
      exact Or.inr (by
        simp only [secondVals, Finset.mem_image, Finset.mem_univ, true_and]
        exact ⟨i, by rw [heq]⟩)
  exact ⟨hdisj, hunion⟩

theorem prevPos_eq_block1 (d : ℕ) (a : Fin (d + 1)) (hpos : 0 < a.val) :
    prevPos d a hpos = block1Pos d a ⟨a.val - 1, by omega⟩ := by
  apply Fin.ext
  simp only [prevPos_val, block1Pos_val]

theorem nextPos_eq_block2 (d : ℕ) (a : Fin (d + 1)) (hlt : a.val < d) :
    nextPos d a hlt = block2Pos d a ⟨1, by omega⟩ := by
  apply Fin.ext
  simp only [nextPos_val, block2Pos_val]

theorem left_failure_of_memA (d : ℕ) (σ : Equiv.Perm (Fin (d + 2)))
    (a : Fin (d + 1))
    (ha : (Finset.univ.filter fun i : Fin (d + 1) =>
      σ i.castSucc < σ i.succ) = {a})
    (hpos : 0 < a.val) (hlt : a.val < d)
    (hA : firstVals d σ a ∈ exclA d a hpos) :
    σ a.succ < σ (prevPos d a hpos) := by
  have htopsub : topSmall d a hpos ⊆ firstVals d σ a := by
    simp only [exclA, Finset.mem_filter] at hA
    exact hA.2
  have hcardL := firstVals_card d σ a
  have hsdiff : (((firstVals d σ a) \ topSmall d a hpos).card) = 1 := by
    have h1 := topSmall_card d a hpos
    have h2 := Finset.card_sdiff_of_subset htopsub
    omega
  obtain ⟨m, hm⟩ := Finset.card_eq_one.mp hsdiff
  have hmem : m ∈ firstVals d σ a ∧ m ∉ topSmall d a hpos := by
    have hmem' : m ∈ firstVals d σ a \ topSmall d a hpos := by
      rw [hm]
      exact Finset.mem_singleton_self m
    exact Finset.mem_sdiff.mp hmem'
  have heqL : firstVals d σ a = insert m (topSmall d a hpos) := by
    ext y
    simp only [Finset.mem_insert]
    constructor
    · intro hy
      by_cases hy2 : y ∈ topSmall d a hpos
      · exact Or.inr hy2
      · have hy3 : y ∈ firstVals d σ a \ topSmall d a hpos :=
          Finset.mem_sdiff.mpr ⟨hy, hy2⟩
        rw [hm] at hy3
        have := Finset.mem_singleton.mp hy3
        exact Or.inl this
    · intro hy
      rcases hy with rfl | hy2
      · exact hmem.1
      · exact htopsub hy2
  have hmin_eq : (firstVals d σ a).min' (firstVals_nonempty d σ a) = m := by
    have hle : ∀ y ∈ firstVals d σ a, m ≤ y := by
      intro y hy
      rw [heqL] at hy
      rcases Finset.mem_insert.mp hy with rfl | hy2
      · exact le_refl _
      · have hmt : m < (⟨d + 2 - a.val, by have ha := a.isLt; omega⟩ :
            Fin (d + 2)) := by
          have hni : m ∉ Finset.Ici (⟨d + 2 - a.val, by
            have ha := a.isLt; omega⟩ : Fin (d + 2)) := by
            have : topSmall d a hpos =
                Finset.Ici (⟨d + 2 - a.val, by
                  have ha := a.isLt; omega⟩ : Fin (d + 2)) := rfl
            rw [this] at hmem
            exact hmem.2
          simp only [Finset.mem_Ici, not_le] at hni
          exact hni
        have hyt : (⟨d + 2 - a.val, by have ha := a.isLt; omega⟩ :
            Fin (d + 2)) ≤ y := by
          have : y ∈ Finset.Ici (⟨d + 2 - a.val, by
            have ha := a.isLt; omega⟩ : Fin (d + 2)) := by
            have : topSmall d a hpos =
                Finset.Ici (⟨d + 2 - a.val, by
                  have ha := a.isLt; omega⟩ : Fin (d + 2)) := rfl
            rw [this] at hy2
            exact hy2
          simp only [Finset.mem_Ici] at this
          exact this
        exact le_of_lt (lt_of_lt_of_le hmt hyt)
    have h1 : (firstVals d σ a).min' (firstVals_nonempty d σ a) ≤ m :=
      Finset.min'_le _ _ hmem.1
    have h2 : m ≤ (firstVals d σ a).min' (firstVals_nonempty d σ a) := by
      have hm2 := Finset.min'_mem (firstVals d σ a) (firstVals_nonempty d σ a)
      exact hle _ hm2
    exact le_antisymm h1 h2
  have hanti1 := block1_anti d σ a ha
  have hprev_mem : σ (prevPos d a hpos) ∈ firstVals d σ a := by
    have heq2 := prevPos_eq_block1 d a hpos
    rw [heq2]
    simp only [firstVals, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨a.val - 1, by omega⟩, rfl⟩
  have hprev_ne : σ (prevPos d a hpos) ≠ m := by
    have hlt_idx : (⟨a.val - 1, by omega⟩ : Fin (a.val + 1)) < Fin.last a.val := by
      simp only [Fin.lt_def, Fin.val_last]
      omega
    have hlt_val : σ (block1Pos d a (Fin.last a.val)) <
        σ (block1Pos d a ⟨a.val - 1, by omega⟩) := hanti1 hlt_idx
    have hmin2 := firstVals_min d σ a ha
    have hbeq : block1Pos d a (Fin.last a.val) = a.castSucc := by
      apply Fin.ext
      simp only [block1Pos_val, Fin.val_castSucc, Fin.val_last]
    rw [hbeq] at hlt_val
    have heq2 := prevPos_eq_block1 d a hpos
    rw [← heq2] at hlt_val
    have hmin3 : (firstVals d σ a).min' (firstVals_nonempty d σ a) =
        σ a.castSucc := hmin2
    rw [hmin_eq] at hmin3
    omega
  have hprev_top : σ (prevPos d a hpos) ∈ topSmall d a hpos := by
    have hmem2 : σ (prevPos d a hpos) ∈ insert m (topSmall d a hpos) := by
      rw [← heqL]
      exact hprev_mem
    rcases Finset.mem_insert.mp hmem2 with heq | hmem3
    · exact absurd heq hprev_ne
    · exact hmem3
  have hmax_mem : σ a.succ ∈ secondVals d σ a := by
    have hmax_eq := secondVals_max d σ a ha
    rw [← hmax_eq]
    exact Finset.max'_mem _ _
  have hdisj := (vals_disjoint_union d σ a).1
  have hdisj2 : Disjoint (topSmall d a hpos) (secondVals d σ a) :=
    Disjoint.mono htopsub (le_refl _) hdisj
  have hmax_ntop : σ a.succ ∉ topSmall d a hpos := by
    have := Finset.disjoint_right.mp hdisj2 hmax_mem
    exact this
  have hlt_max : σ a.succ < (⟨d + 2 - a.val, by
      have ha := a.isLt; omega⟩ : Fin (d + 2)) := by
    have hni : σ a.succ ∉ Finset.Ici (⟨d + 2 - a.val, by
        have ha := a.isLt; omega⟩ : Fin (d + 2)) := by
      have : topSmall d a hpos =
          Finset.Ici (⟨d + 2 - a.val, by
            have ha := a.isLt; omega⟩ : Fin (d + 2)) := rfl
      rw [this] at hmax_ntop
      exact hmax_ntop
    simp only [Finset.mem_Ici, not_le] at hni
    exact hni
  have hge_prev : (⟨d + 2 - a.val, by have ha := a.isLt; omega⟩ :
      Fin (d + 2)) ≤ σ (prevPos d a hpos) := by
    have : σ (prevPos d a hpos) ∈ Finset.Ici (⟨d + 2 - a.val, by
        have ha := a.isLt; omega⟩ : Fin (d + 2)) := by
      have : topSmall d a hpos =
          Finset.Ici (⟨d + 2 - a.val, by
            have ha := a.isLt; omega⟩ : Fin (d + 2)) := rfl
      rw [this] at hprev_top
      exact hprev_top
    simp only [Finset.mem_Ici] at this
    exact this
  exact lt_of_lt_of_le hlt_max hge_prev

theorem right_failure_of_memB (d : ℕ) (σ : Equiv.Perm (Fin (d + 2)))
    (a : Fin (d + 1))
    (ha : (Finset.univ.filter fun i : Fin (d + 1) =>
      σ i.castSucc < σ i.succ) = {a})
    (hpos : 0 < a.val) (hlt : a.val < d)
    (hB : firstVals d σ a ∈ exclB d a) :
    σ (nextPos d a hlt) < σ a.castSucc := by
  have hsubL : firstVals d σ a ⊆ topLarge d a := by
    simp only [exclB, Finset.mem_filter] at hB
    exact hB.2
  have hdisjU := vals_disjoint_union d σ a
  have hcompl : secondVals d σ a = (firstVals d σ a)ᶜ := by
    ext y
    simp only [Finset.mem_compl]
    constructor
    · intro hy
      have := Finset.disjoint_right.mp hdisjU.1 hy
      exact this
    · intro hy
      have hun : y ∈ firstVals d σ a ∪ secondVals d σ a := by
        rw [hdisjU.2]
        exact Finset.mem_univ y
      simp only [Finset.mem_union] at hun
      rcases hun with h1 | h2
      · exact absurd h1 hy
      · exact h2
  have hbot_sub : Finset.Iio (⟨d - a.val, by omega⟩ : Fin (d + 2)) ⊆
      secondVals d σ a := by
    intro y hy
    simp only [Finset.mem_Iio] at hy
    rw [hcompl]
    simp only [Finset.mem_compl]
    intro hyL
    have hyT : y ∈ topLarge d a := hsubL hyL
    simp only [topLarge, Finset.mem_Ici] at hyT
    have hle : (⟨d - a.val, by omega⟩ : Fin (d + 2)) ≤ y := hyT
    exact absurd (lt_of_lt_of_le hy hle) (lt_irrefl _)
  have hcardR := secondVals_card d σ a
  have hcardB : (Finset.Iio (⟨d - a.val, by omega⟩ : Fin (d + 2))).card =
      d - a.val := by
    simp only [Fin.card_Iio]
  have hsdiff : ((secondVals d σ a \
      Finset.Iio (⟨d - a.val, by omega⟩ : Fin (d + 2))).card) = 1 := by
    have h2 := Finset.card_sdiff_of_subset hbot_sub
    omega
  obtain ⟨M, hM⟩ := Finset.card_eq_one.mp hsdiff
  have hmemM : M ∈ secondVals d σ a ∧
      M ∉ Finset.Iio (⟨d - a.val, by omega⟩ : Fin (d + 2)) := by
    have hmem' : M ∈ secondVals d σ a \
        Finset.Iio (⟨d - a.val, by omega⟩ : Fin (d + 2)) := by
      rw [hM]
      exact Finset.mem_singleton_self M
    exact Finset.mem_sdiff.mp hmem'
  have heqR : secondVals d σ a =
      insert M (Finset.Iio (⟨d - a.val, by omega⟩ : Fin (d + 2))) := by
    ext y
    simp only [Finset.mem_insert]
    constructor
    · intro hy
      by_cases hy2 : y ∈ Finset.Iio (⟨d - a.val, by omega⟩ : Fin (d + 2))
      · exact Or.inr hy2
      · have hy3 : y ∈ secondVals d σ a \
            Finset.Iio (⟨d - a.val, by omega⟩ : Fin (d + 2)) :=
          Finset.mem_sdiff.mpr ⟨hy, hy2⟩
        rw [hM] at hy3
        have := Finset.mem_singleton.mp hy3
        exact Or.inl this
    · intro hy
      rcases hy with rfl | hy2
      · exact hmemM.1
      · exact hbot_sub hy2
  have hMge : (⟨d - a.val, by omega⟩ : Fin (d + 2)) ≤ M := by
    have hni := hmemM.2
    simp only [Finset.mem_Iio, not_lt] at hni
    exact hni
  have hmax_eq : M =
      (secondVals d σ a).max' (secondVals_nonempty d σ a) := by
    have hle : ∀ y ∈ secondVals d σ a, y ≤ M := by
      intro y hy
      rw [heqR] at hy
      rcases Finset.mem_insert.mp hy with rfl | hy2
      · exact le_refl _
      · have hlt : y < (⟨d - a.val, by omega⟩ : Fin (d + 2)) :=
          Finset.mem_Iio.mp hy2
        exact le_of_lt (lt_of_lt_of_le hlt hMge)
    have h1 : M ≤ (secondVals d σ a).max' (secondVals_nonempty d σ a) :=
      Finset.le_max' _ _ hmemM.1
    have h2 : (secondVals d σ a).max' (secondVals_nonempty d σ a) ≤ M := by
      have hm := Finset.max'_mem (secondVals d σ a) (secondVals_nonempty d σ a)
      exact hle _ hm
    exact le_antisymm h1 h2
  have hanti2 := block2_anti d σ a ha
  have hnext_mem : σ (nextPos d a hlt) ∈ secondVals d σ a := by
    have heq2 := nextPos_eq_block2 d a hlt
    rw [heq2]
    simp only [secondVals, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨1, by omega⟩, rfl⟩
  have hnext_ne : σ (nextPos d a hlt) ≠ M := by
    have hlt_idx : (0 : Fin ((d - a.val) + 1)) < ⟨1, by omega⟩ := by
      simp only [Fin.lt_def, Fin.val_zero]
      omega
    have hlt_val : σ (block2Pos d a ⟨1, by omega⟩) <
        σ (block2Pos d a 0) := hanti2 hlt_idx
    have heq2 := nextPos_eq_block2 d a hlt
    have hz : block2Pos d a (0 : Fin ((d - a.val) + 1)) = a.succ := by
      apply Fin.ext
      simp only [block2Pos_val, Fin.val_succ, Fin.val_zero]
    rw [← heq2] at hlt_val
    rw [hz] at hlt_val
    have hmax2 := secondVals_max d σ a ha
    rw [← hmax_eq] at hmax2
    rw [hmax2]
    exact ne_of_lt hlt_val
  have hnext_bot : σ (nextPos d a hlt) ∈
      Finset.Iio (⟨d - a.val, by omega⟩ : Fin (d + 2)) := by
    have hmem2 : σ (nextPos d a hlt) ∈
        insert M (Finset.Iio (⟨d - a.val, by omega⟩ : Fin (d + 2))) := by
      rw [← heqR]
      exact hnext_mem
    rcases Finset.mem_insert.mp hmem2 with heq | hmem3
    · exact absurd heq hnext_ne
    · exact hmem3
  have hmin_mem : (firstVals d σ a).min' (firstVals_nonempty d σ a) ∈
      topLarge d a := hsubL (Finset.min'_mem _ _)
  have hmin_ge : (⟨d - a.val, by omega⟩ : Fin (d + 2)) ≤
      (firstVals d σ a).min' (firstVals_nonempty d σ a) := by
    have : (firstVals d σ a).min' (firstVals_nonempty d σ a) ∈
        Finset.Ici (⟨d - a.val, by omega⟩ : Fin (d + 2)) := by
      have : topLarge d a =
          Finset.Ici (⟨d - a.val, by omega⟩ : Fin (d + 2)) := rfl
      rw [this] at hmin_mem
      exact hmin_mem
    simp only [Finset.mem_Ici] at this
    exact this
  have hnext_lt : σ (nextPos d a hlt) <
      (⟨d - a.val, by omega⟩ : Fin (d + 2)) :=
    Finset.mem_Iio.mp hnext_bot
  have hmin_eq := firstVals_min d σ a ha
  calc σ (nextPos d a hlt)
      < (⟨d - a.val, by omega⟩ : Fin (d + 2)) := hnext_lt
    _ ≤ (firstVals d σ a).min' (firstVals_nonempty d σ a) := hmin_ge
    _ = σ a.castSucc := hmin_eq

theorem mpe_prev_le_threshold (d : ℕ) (σ : Equiv.Perm (Fin (d + 2)))
    (a : Fin (d + 1))
    (ha : (Finset.univ.filter fun i : Fin (d + 1) =>
      σ i.castSucc < σ i.succ) = {a})
    (hpos : 0 < a.val) :
    (σ (prevPos d a hpos)).val ≤ d + 2 - a.val := by
  let s := Finset.image
    (fun i : Fin a.val => σ (block1Pos d a i.castSucc)) Finset.univ
  have hcard : s.card = a.val := by
    rw [Finset.card_image_of_injective]
    · simp only [Finset.card_univ, Fintype.card_fin]
    · intro i j hij
      apply Fin.ext
      have hv := congrArg Fin.val (block1Pos_inj d a (σ.injective hij))
      simpa only [Fin.val_castSucc] using hv
  have hsub : s ⊆ Finset.Ici (σ (prevPos d a hpos)) := by
    intro y hy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
    simp only [Finset.mem_Ici]
    have hle : i.castSucc ≤ (⟨a.val - 1, by omega⟩ : Fin (a.val + 1)) := by
      change i.val ≤ a.val - 1
      omega
    rw [prevPos_eq_block1 d a hpos]
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact le_of_lt (block1_anti d σ a ha hlt)
    · rw [heq]
  have hle := Finset.card_le_card hsub
  rw [hcard] at hle
  simp only [Fin.card_Ici] at hle
  omega

theorem mpe_mem_exclA_of_left_failure (d : ℕ)
    (σ : Equiv.Perm (Fin (d + 2))) (a : Fin (d + 1))
    (ha : (Finset.univ.filter fun i : Fin (d + 1) =>
      σ i.castSucc < σ i.succ) = {a})
    (hpos : 0 < a.val)
    (hfail : σ a.succ < σ (prevPos d a hpos)) :
    firstVals d σ a ∈ exclA d a hpos := by
  have htop : topSmall d a hpos ⊆ firstVals d σ a := by
    intro x hx
    by_contra hxL
    have hun : x ∈ firstVals d σ a ∪ secondVals d σ a := by
      rw [(vals_disjoint_union d σ a).2]
      exact Finset.mem_univ x
    have hxR : x ∈ secondVals d σ a := by
      rcases Finset.mem_union.mp hun with hx' | hx'
      · exact absurd hx' hxL
      · exact hx'
    have hxle : x ≤ σ a.succ := by
      rw [← secondVals_max d σ a ha]
      exact Finset.le_max' _ _ hxR
    have hxprev : x < σ (prevPos d a hpos) := lt_of_le_of_lt hxle hfail
    have hxge : d + 2 - a.val ≤ x.val := by
      simp only [topSmall, Finset.mem_Ici] at hx
      change d + 2 - a.val ≤ x.val at hx
      exact hx
    have hp := mpe_prev_le_threshold d σ a ha hpos
    exact (by omega)
  simp only [exclA, Finset.mem_filter, Finset.mem_powersetCard]
  exact ⟨⟨Finset.subset_univ _, firstVals_card d σ a⟩, htop⟩

theorem mpe_threshold_le_next_succ (d : ℕ) (σ : Equiv.Perm (Fin (d + 2)))
    (a : Fin (d + 1))
    (ha : (Finset.univ.filter fun i : Fin (d + 1) =>
      σ i.castSucc < σ i.succ) = {a})
    (hlt : a.val < d) :
    d - a.val ≤ (σ (nextPos d a hlt)).val + 1 := by
  let s := Finset.image
    (fun i : Fin (d - a.val) => σ (block2Pos d a i.succ)) Finset.univ
  have hcard : s.card = d - a.val := by
    rw [Finset.card_image_of_injective]
    · simp only [Finset.card_univ, Fintype.card_fin]
    · intro i j hij
      apply Fin.ext
      have hv := congrArg Fin.val (block2Pos_inj d a (σ.injective hij))
      simp only [Fin.val_succ] at hv
      omega
  have hsub : s ⊆ Finset.Iic (σ (nextPos d a hlt)) := by
    intro y hy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
    simp only [Finset.mem_Iic]
    have hle : (⟨1, by omega⟩ : Fin ((d - a.val) + 1)) ≤ i.succ := by
      change 1 ≤ i.val + 1
      omega
    rw [nextPos_eq_block2 d a hlt]
    rcases lt_or_eq_of_le hle with hlt' | heq
    · exact le_of_lt (block2_anti d σ a ha hlt')
    · rw [heq]
  have hle := Finset.card_le_card hsub
  rw [hcard] at hle
  simpa only [Fin.card_Iic] using hle

theorem mpe_mem_exclB_of_right_failure (d : ℕ)
    (σ : Equiv.Perm (Fin (d + 2))) (a : Fin (d + 1))
    (ha : (Finset.univ.filter fun i : Fin (d + 1) =>
      σ i.castSucc < σ i.succ) = {a})
    (hlt : a.val < d)
    (hfail : σ (nextPos d a hlt) < σ a.castSucc) :
    firstVals d σ a ∈ exclB d a := by
  have htail := mpe_threshold_le_next_succ d σ a ha hlt
  have hmin : d - a.val ≤ (σ a.castSucc).val := by
    omega
  have hsub : firstVals d σ a ⊆ topLarge d a := by
    intro x hx
    have hminle : σ a.castSucc ≤ x := by
      rw [← firstVals_min d σ a ha]
      exact Finset.min'_le _ _ hx
    simp only [topLarge, Finset.mem_Ici]
    change d - a.val ≤ x.val
    omega
  simp only [exclB, Finset.mem_filter, Finset.mem_powersetCard]
  exact ⟨⟨Finset.subset_univ _, firstVals_card d σ a⟩, hsub⟩

end MetaMathlibExt
end
