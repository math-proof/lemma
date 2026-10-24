import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


section
variable {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

private lemma v_sub_comm
  {a b : K} :
  Valued.v (a - b) = Valued.v (b - a) :=
  Valuation.map_sub_swap _ a b

private lemma v_sub_le_max
  {a b c : K} :
  Valued.v (a - c) ≤ max (Valued.v (a - b)) (Valued.v (b - c)) := by
  have : a - c = (a - b) + (b - c) := by
    ring
  rw [this]
  apply Valuation.map_add _ _ _

private lemma v_sub_eq_of_lt
  {a b c : K}
  (h : Valued.v (a - b) < Valued.v (b - c)) :
  Valued.v (a - c) = Valued.v (b - c) := by
  have : a - c = (a - b) + (b - c) := by
    ring
  rw [this]
  apply Valuation.map_add_eq_of_lt_right _ h

private lemma exists_maxSel
  {F : K → Finset K} :
  ∃ g : K → K, ∀ h : K, (F h).Nonempty → g h ∈ F h ∧ ∀ x ∈ F h, Valued.v x ≤ Valued.v (g h) := by
  classical
  have : ∀ h : K, ∃ y : K, ((F h).Nonempty → y ∈ F h ∧ ∀ x ∈ F h, Valued.v x ≤ Valued.v y) := by
    intro h
    if hne : (F h).Nonempty then
      obtain ⟨y, hy, hmax⟩ := Finset.exists_max_image (F h) (fun x => Valued.v x) hne
      exact ⟨y, fun _ => ⟨hy, hmax⟩⟩
    else
      exact ⟨1, fun h' => (hne h').elim⟩
  choose g hg using this
  exact ⟨g, hg⟩

end
/--
[CerednikDrinfeld_Omega_linearPiece_eq_empty_or_exists_tube_and_closedDisc_subset](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_CerednikDrinfeld_Omega_linearPiece_eq_empty_or_exists_tube_and_closedDisc_subset.lean)
-/
@[path]
private lemma main
  {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
  {c₀ R₀ : K} {H : Finset K} {ρ : K → K} {P : Set K}
  {L M : Finset (K × K)} {Q : Set K}
  (hnt : ∃ y : K, y ≠ 0 ∧ Valued.v y < 1)
  (hR₀ : R₀ ≠ 0)
  (hρ : ∀ h ∈ H, ρ h ≠ 0)
  (hP : ∀ z : K, z ∈ P ↔ Valued.v (z - c₀) ≤ Valued.v R₀ ∧ ∀ h ∈ H, Valued.v (ρ h) ≤ Valued.v (z - h))
  (hL : ∀ er ∈ L, er.2 ≠ 0)
  (hM : ∀ er ∈ M, er.2 ≠ 0)
  (hQ : ∀ z : K, z ∈ Q ↔ z ∈ P ∧ (∀ er ∈ L, Valued.v er.2 ≤ Valued.v (z - er.1)) ∧
    (∀ er ∈ M, Valued.v (z - er.1) ≤ Valued.v er.2)) :
  ((∀ z : K, z ∉ Q) ∨
    ∃ (c₁ R₁ : K) (H₁ : Finset K) (ρ₁ : K → K), R₁ ≠ 0 ∧ (∀ h ∈ H₁, ρ₁ h ≠ 0) ∧
      ∀ z : K, z ∈ Q ↔ Valued.v (z - c₁) ≤ Valued.v R₁ ∧ ∀ h ∈ H₁, Valued.v (ρ₁ h) ≤ Valued.v (z - h)) ∧
    (∀ z ∈ Q, ∃ r : K, r ≠ 0 ∧ ∀ w : K, Valued.v (w - z) ≤ Valued.v r → w ∈ Q) := by
  classical
  obtain ⟨y, hy0, hy1⟩ := hnt
  refine ⟨?_, ?_⟩
  ·
    if hQe : ∀ z : K, z ∉ Q then
      apply Or.inl hQe
    else
      right
      push Not at hQe
      obtain ⟨q, hq⟩ := hQe
      obtain ⟨hqP, hqL, hqM⟩ := (hQ q).mp hq
      obtain ⟨hqc, hqH⟩ := (hP q).mp hqP
      let Ds : Finset (K × K) := insert (c₀, R₀) M
      have hDs0 : ∀ d ∈ Ds, d.2 ≠ 0 := by
        intro d hd
        obtain rfl | hd := Finset.mem_insert.mp hd
        · apply hR₀
        · apply hM d hd
      have hqDs : ∀ d ∈ Ds, Valued.v (q - d.1) ≤ Valued.v d.2 := by
        intro d hd
        obtain rfl | hd := Finset.mem_insert.mp hd
        · apply hqc
        · apply hqM d hd
      obtain ⟨d₁, hd₁, hmin⟩ := Finset.exists_min_image Ds (fun d => Valued.v d.2) ⟨(c₀, R₀), Finset.mem_insert_self _ _⟩
      let H₁ : Finset K := H ∪ L.image Prod.fst
      let Rad : K → Finset K := fun h => (H.filter (fun h' => h' = h)).image ρ ∪ (L.filter (fun er => er.1 = h)).image Prod.snd
      obtain ⟨ρ₁, hρ₁⟩ := exists_maxSel (F := Rad)
      have hRadH : ∀ h ∈ H, ρ h ∈ Rad h := fun h hh =>
        Finset.mem_union_left _ (Finset.mem_image.mpr ⟨h, Finset.mem_filter.mpr ⟨hh, rfl⟩, rfl⟩)
      have hRadL : ∀ er ∈ L, er.2 ∈ Rad er.1 := fun er her =>
        Finset.mem_union_right _ (Finset.mem_image.mpr ⟨er, Finset.mem_filter.mpr ⟨her, rfl⟩, rfl⟩)
      have hRad_cases : ∀ (h x : K), x ∈ Rad h → (h ∈ H ∧ x = ρ h) ∨ (∃ er ∈ L, er.1 = h ∧ er.2 = x) := by
        intro h x hx
        obtain hx | hx := Finset.mem_union.mp hx
        ·
          obtain ⟨h', hh', rfl⟩ := Finset.mem_image.mp hx
          obtain ⟨hh'H, rfl⟩ := Finset.mem_filter.mp hh'
          apply Or.inl ⟨hh'H, rfl⟩
        ·
          obtain ⟨er, her, rfl⟩ := Finset.mem_image.mp hx
          obtain ⟨herL, h1⟩ := Finset.mem_filter.mp her
          apply Or.inr ⟨er, herL, h1, rfl⟩
      have hRadne : ∀ h ∈ H₁, (Rad h).Nonempty := by
        intro h hh
        obtain hh | hh := Finset.mem_union.mp hh
        · exact ⟨ρ h, hRadH h hh⟩
        ·
          obtain ⟨er, her, rfl⟩ := Finset.mem_image.mp hh
          exact ⟨er.2, hRadL er her⟩
      refine ⟨d₁.1, d₁.2, H₁, ρ₁, hDs0 d₁ hd₁, ?_, ?_⟩
      ·
        intro h hh
        obtain ⟨hmem, -⟩ := hρ₁ h (hRadne h hh)
        obtain ⟨hH, e⟩ | ⟨er, her, -, e⟩ := hRad_cases h _ hmem
        ·
          rw [e]
          apply hρ h hH
        ·
          rw [← e]
          apply hL er her
      intro z
      constructor
      ·
        intro hz
        obtain ⟨hzP, hzL, hzM⟩ := (hQ z).mp hz
        obtain ⟨hzc, hzH⟩ := (hP z).mp hzP
        refine ⟨?_, fun h hh => ?_⟩
        ·
          obtain rfl | hd := Finset.mem_insert.mp hd₁
          · apply hzc
          · apply hzM d₁ hd
        ·
          obtain ⟨hmem, -⟩ := hρ₁ h (hRadne h hh)
          obtain ⟨hH, e⟩ | ⟨er, her, e1, e⟩ := hRad_cases h _ hmem
          ·
            rw [e]
            apply hzH h hH
          ·
            rw [← e, ← e1]
            apply hzL er her
      ·
        rintro ⟨hzc₁, hzH₁⟩
        have hswap : Valued.v (d₁.1 - q) ≤ Valued.v d₁.2 := by
          rw [v_sub_comm]
          apply hqDs d₁ hd₁
        have hzq : Valued.v (z - q) ≤ Valued.v d₁.2 :=
          (v_sub_le_max (a := z) (b := d₁.1) (c := q)).trans (max_le hzc₁ hswap)
        have hzDs : ∀ d ∈ Ds, Valued.v (z - d.1) ≤ Valued.v d.2 := fun d hd =>
          (v_sub_le_max (a := z) (b := q) (c := d.1)).trans (max_le (hzq.trans (hmin d hd)) (hqDs d hd))
        have hlow : ∀ h ∈ H₁, ∀ x ∈ Rad h, Valued.v x ≤ Valued.v (z - h) := fun h hh x hx =>
          ((hρ₁ h (hRadne h hh)).2 x hx).trans (hzH₁ h hh)
        rw [hQ, hP]
        refine ⟨⟨hzDs _ (Finset.mem_insert_self _ _), fun h hh => ?_⟩, fun er her => ?_, fun er her => hzDs er (Finset.mem_insert_of_mem her)⟩
        · apply hlow h (Finset.mem_union_left _ hh) _ (hRadH h hh)
        · apply hlow er.1 (Finset.mem_union_right _ (Finset.mem_image_of_mem _ her)) _ (hRadL er her)
  ·
    intro z hz
    obtain ⟨hzP, hzL, hzM⟩ := (hQ z).mp hz
    obtain ⟨hzc, hzH⟩ := (hP z).mp hzP
    let Gz : Finset K := insert R₀ ((M.image Prod.snd ∪ H.image (fun h => z - h)) ∪ L.image (fun er => z - er.1))
    obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image Gz (fun x => Valued.v x) ⟨R₀, Finset.mem_insert_self _ _⟩
    have hm0 : m ≠ 0 := by
      obtain rfl | hm' := Finset.mem_insert.mp hm
      · apply hR₀
      ·
        obtain hm' | hm' := Finset.mem_union.mp hm'
        ·
          obtain hm' | hm' := Finset.mem_union.mp hm'
          ·
            obtain ⟨er, her, rfl⟩ := Finset.mem_image.mp hm'
            apply hM er her
          ·
            obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hm'
            intro h0
            have := hzH h hh
            rw [h0, Valuation.map_zero, le_zero_iff] at this
            apply hρ h hh ((Valuation.zero_iff _).mp this)
        ·
          obtain ⟨er, her, rfl⟩ := Finset.mem_image.mp hm'
          intro h0
          have := hzL er her
          rw [h0, Valuation.map_zero, le_zero_iff] at this
          apply hL er her ((Valuation.zero_iff _).mp this)
    have hvm : 0 < Valued.v m := (Valuation.pos_iff _).mpr hm0
    refine ⟨y * m, mul_ne_zero hy0 hm0, fun w hw => ?_⟩
    have hwz : Valued.v (w - z) < Valued.v m := by
      rw [Valuation.map_mul] at hw
      have : Valued.v y * Valued.v m < 1 * Valued.v m := mul_lt_mul_of_pos_right hy1 hvm
      rw [one_mul] at this
      apply lt_of_le_of_lt hw this
    have hwz' : ∀ x ∈ Gz, Valued.v (w - z) < Valued.v x := fun x hx => lt_of_lt_of_le hwz (hmin x hx)
    rw [hQ, hP]
    refine ⟨⟨?_, fun h hh => ?_⟩, fun er her => ?_, fun er her => ?_⟩
    · apply (v_sub_le_max (a := w) (b := z) (c := c₀)).trans (max_le (hwz' R₀ (Finset.mem_insert_self _ _)).le hzc)
    ·
      have : Valued.v (w - z) < Valued.v (z - h) :=
        hwz' _ (Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hh))))
      rw [v_sub_eq_of_lt this]
      apply hzH h hh
    ·
      have : Valued.v (w - z) < Valued.v (z - er.1) :=
        hwz' _ (Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image_of_mem _ her)))
      rw [v_sub_eq_of_lt this]
      apply hzL er her
    · apply (v_sub_le_max (a := w) (b := z) (c := er.1)).trans (max_le
        (hwz' _ (Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ her))))).le
        (hzM er her))


-- created on 2026-10-20
