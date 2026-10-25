/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/BellWeakExcedance.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Combinatorics.Enumerative.Bell
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.Bound
import Mathlib.Order.Partition.Finpartition
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Def.Combinatorics.BellWeakExcedance.Part8


section

namespace MetaMathlibExt

theorem minOfBlock_mem_mins {n : ℕ}
    {P : Finpartition (Finset.univ : Finset (Fin n))} {x : Fin n} :
    minOfBlock P x ∈ mins P := by
  rw [mem_mins_iff]
  refine ⟨P.part x, P.part_mem.mpr (Finset.mem_univ x), ?_, ?_⟩
  · unfold minOfBlock
    exact Finset.min'_mem _ _
  · intro y hy
    unfold minOfBlock
    exact Finset.min'_le _ _ hy

theorem minOfBlock_le {n : ℕ}
    {P : Finpartition (Finset.univ : Finset (Fin n))} {x : Fin n} :
    minOfBlock P x ≤ x := by
  unfold minOfBlock
  exact Finset.min'_le _ _ (P.mem_part (Finset.mem_univ x))

theorem maxs_le_mins_card {n : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin n))) (t : Fin n) :
    ((maxs P).filter (fun x => x ≤ t)).card ≤
      ((mins P).filter (fun m => m ≤ t)).card := by
  have hmaps : Set.MapsTo (minOfBlock P)
      ((maxs P).filter (fun x => x ≤ t)) ((mins P).filter (fun m => m ≤ t)) := by
    intro x hx
    rw [Finset.mem_coe, Finset.mem_filter] at hx ⊢
    obtain ⟨hxmax, hxt⟩ := hx
    constructor
    · exact minOfBlock_mem_mins
    · exact le_trans (minOfBlock_le) hxt
  have hinj : Set.InjOn (minOfBlock P) ((maxs P).filter (fun x => x ≤ t)) := by
    intro x1 hx1 x2 hx2 hEq
    rw [Finset.mem_coe, Finset.mem_filter] at hx1 hx2
    obtain ⟨hx1max, -⟩ := hx1
    obtain ⟨hx2max, -⟩ := hx2
    rw [mem_maxs_iff] at hx1max hx2max
    obtain ⟨t1, ht1, hmem1, hle1⟩ := hx1max
    obtain ⟨t2, ht2, hmem2, hle2⟩ := hx2max
    have hpart1 : P.part x1 = t1 := P.part_eq_of_mem ht1 hmem1
    have hpart2 : P.part x2 = t2 := P.part_eq_of_mem ht2 hmem2
    have hmin1_mem : minOfBlock P x1 ∈ P.part x1 := by
      unfold minOfBlock
      exact Finset.min'_mem _ _
    have hmin2_mem : minOfBlock P x2 ∈ P.part x2 := by
      unfold minOfBlock
      exact Finset.min'_mem _ _
    have htEq : t1 = t2 := by
      have h1 : P.part x1 ∈ P.parts := P.part_mem.mpr (Finset.mem_univ x1)
      have h2 : P.part x2 ∈ P.parts := P.part_mem.mpr (Finset.mem_univ x2)
      have hmem1' : minOfBlock P x1 ∈ P.part x1 := hmin1_mem
      have hmem2' : minOfBlock P x1 ∈ P.part x2 := hEq ▸ hmin2_mem
      have hpeq : P.part x1 = P.part x2 :=
        P.eq_of_mem_parts h1 h2 hmem1' hmem2'
      rw [hpart1, hpart2] at hpeq
      exact hpeq
    subst htEq
    apply le_antisymm
    · exact hle2 x1 hmem1
    · exact hle1 x2 hmem2
  exact Finset.card_le_card_of_injOn _ hmaps hinj

theorem interlacing {n : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin n))) :
    ∀ i : Fin P.parts.card,
      (mins P).orderEmbOfFin (card_mins_eq P) i ≤
        (maxs P).orderEmbOfFin (card_maxs_eq P) i := by
  intro i
  by_contra hlt
  have hgt : (maxs P).orderEmbOfFin (card_maxs_eq P) i <
      (mins P).orderEmbOfFin (card_mins_eq P) i :=
    lt_of_not_ge hlt
  set t : Fin n := (maxs P).orderEmbOfFin (card_maxs_eq P) i with ht
  have hdom := maxs_le_mins_card P t
  -- lower bound for maxs filter via Iic i
  have hmaps_max : Set.MapsTo ((maxs P).orderEmbOfFin (card_maxs_eq P))
      (Finset.Iic i) ((maxs P).filter (fun x => x ≤ t)) := by
    intro j hj
    rw [Finset.mem_coe, Finset.mem_Iic] at hj
    rw [Finset.mem_coe, Finset.mem_filter]
    constructor
    · exact Finset.orderEmbOfFin_mem _ _ _
    · have hle : j ≤ i := hj
      have hmono : (maxs P).orderEmbOfFin (card_maxs_eq P) j ≤
          (maxs P).orderEmbOfFin (card_maxs_eq P) i :=
        (OrderEmbedding.monotone _ hle)
      rw [ht]
      exact hmono
  have hinj_max : Set.InjOn ((maxs P).orderEmbOfFin (card_maxs_eq P))
      (Finset.Iic i) := by
    intro j1 hj1 j2 hj2 hEq
    have hle1 : j1 ≤ j2 := by
      have hle : (maxs P).orderEmbOfFin (card_maxs_eq P) j1 ≤
          (maxs P).orderEmbOfFin (card_maxs_eq P) j2 := le_of_eq hEq
      exact ((maxs P).orderEmbOfFin (card_maxs_eq P)).le_iff_le.mp hle
    have hle2 : j2 ≤ j1 := by
      have hle : (maxs P).orderEmbOfFin (card_maxs_eq P) j2 ≤
          (maxs P).orderEmbOfFin (card_maxs_eq P) j1 := le_of_eq hEq.symm
      exact ((maxs P).orderEmbOfFin (card_maxs_eq P)).le_iff_le.mp hle
    exact le_antisymm hle1 hle2
  have hcard_ge : (Finset.Iic i).card ≤
      ((maxs P).filter (fun x => x ≤ t)).card :=
    Finset.card_le_card_of_injOn _ hmaps_max hinj_max
  -- upper bound: filter_min ⊆ image eM (Iio i)
  have hsub_min : (mins P).filter (fun m => m ≤ t) ⊆
      (Finset.Iio i).image ((mins P).orderEmbOfFin (card_mins_eq P)) := by
    intro m hm
    rw [Finset.mem_filter] at hm
    obtain ⟨hmM, hmt⟩ := hm
    have ht_lt : t < (mins P).orderEmbOfFin (card_mins_eq P) i := by
      rw [ht]
      exact hgt
    have hm_lt : m < (mins P).orderEmbOfFin (card_mins_eq P) i :=
      lt_of_le_of_lt hmt ht_lt
    have hj : ∃ j : Fin P.parts.card,
        j ∈ Finset.Iio i ∧
          (mins P).orderEmbOfFin (card_mins_eq P) j = m := by
      have hmem : m ∈ mins P := hmM
      refine ⟨((mins P).orderIsoOfFin (card_mins_eq P)).symm ⟨m, hmem⟩, ?_, ?_⟩
      · rw [Finset.mem_Iio]
        have heq : (mins P).orderEmbOfFin (card_mins_eq P)
            (((mins P).orderIsoOfFin (card_mins_eq P)).symm ⟨m, hmem⟩) = m := by
          have h1 : ((mins P).orderIsoOfFin (card_mins_eq P))
              (((mins P).orderIsoOfFin (card_mins_eq P)).symm ⟨m, hmem⟩) =
              ⟨m, hmem⟩ :=
            OrderIso.apply_symm_apply _ _
          have h2 : ↑(((mins P).orderIsoOfFin (card_mins_eq P))
              (((mins P).orderIsoOfFin (card_mins_eq P)).symm ⟨m, hmem⟩)) = m := by
            rw [h1]
          rw [Finset.coe_orderIsoOfFin_apply] at h2
          exact h2
        have hlt : (mins P).orderEmbOfFin (card_mins_eq P)
            (((mins P).orderIsoOfFin (card_mins_eq P)).symm ⟨m, hmem⟩) <
            (mins P).orderEmbOfFin (card_mins_eq P) i := by
          rw [heq]
          exact hm_lt
        exact ((mins P).orderEmbOfFin (card_mins_eq P)).lt_iff_lt.mp hlt
      · have h1 : ((mins P).orderIsoOfFin (card_mins_eq P))
            (((mins P).orderIsoOfFin (card_mins_eq P)).symm ⟨m, hmem⟩) =
            ⟨m, hmem⟩ :=
          OrderIso.apply_symm_apply _ _
        have h2 : ↑(((mins P).orderIsoOfFin (card_mins_eq P))
            (((mins P).orderIsoOfFin (card_mins_eq P)).symm ⟨m, hmem⟩)) = m := by
          rw [h1]
        rw [Finset.coe_orderIsoOfFin_apply] at h2
        exact h2
    obtain ⟨j, hjIio, heq⟩ := hj
    rw [Finset.mem_image]
    exact ⟨j, hjIio, heq⟩
  have hinj_min : Set.InjOn ((mins P).orderEmbOfFin (card_mins_eq P))
      (Finset.Iio i) := by
    intro j1 hj1 j2 hj2 hEq
    have hle1 : j1 ≤ j2 := by
      have hle : (mins P).orderEmbOfFin (card_mins_eq P) j1 ≤
          (mins P).orderEmbOfFin (card_mins_eq P) j2 := le_of_eq hEq
      exact ((mins P).orderEmbOfFin (card_mins_eq P)).le_iff_le.mp hle
    have hle2 : j2 ≤ j1 := by
      have hle : (mins P).orderEmbOfFin (card_mins_eq P) j2 ≤
          (mins P).orderEmbOfFin (card_mins_eq P) j1 := le_of_eq hEq.symm
      exact ((mins P).orderEmbOfFin (card_mins_eq P)).le_iff_le.mp hle
    exact le_antisymm hle1 hle2
  have hcard_image : ((Finset.Iio i).image
      ((mins P).orderEmbOfFin (card_mins_eq P))).card = (Finset.Iio i).card :=
    Finset.card_image_of_injOn hinj_min
  have hcard_le : ((mins P).filter (fun m => m ≤ t)).card ≤
      (Finset.Iio i).card := by
    calc ((mins P).filter (fun m => m ≤ t)).card ≤
          ((Finset.Iio i).image
            ((mins P).orderEmbOfFin (card_mins_eq P))).card :=
          Finset.card_le_card hsub_min
      _ = (Finset.Iio i).card := hcard_image
  have hIic : (Finset.Iic i).card = i.val + 1 := by simp
  have hIio : (Finset.Iio i).card = i.val := by simp
  omega

end MetaMathlibExt
end
