/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PollakPartialParkingFunctions.lean -/

import Mathlib.Data.Finset.Card
import Mathlib.SetTheory.Cardinal.Finite
import Instance.Combinatorics.Enumerative.ParkingFunction
import Lemma.Finset.Enumerative.ParkingFunction
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Def.Combinatorics.Enumerative.PollakPartialParkingFunctions.Part8


namespace MetaMathlibExt.PollakPartialParking

theorem linAssign_spec (s t : ℕ) (f : Fin s → Fin t)
    (hsucc : LinSuccess s t f) (j : Fin s) :
    linTake s t f j.val j.isLt = some (linAssign s t f hsucc j) :=
  (linTake_some_of_success s t f hsucc j.val j.isLt).choose_spec

theorem linAssign_ge (s t : ℕ) (f : Fin s → Fin t)
    (hsucc : LinSuccess s t f) (j : Fin s) : f j ≤ linAssign s t f hsucc j := by
  have htake := linAssign_spec s t f hsucc j
  have h0 := linOccAux_some_of_le s t f j.val (by omega) hsucc
  obtain ⟨occ, hocc⟩ := linOccAux_eq_some_of_isSome s t f j.val h0
  rw [linTake_eq s t f j.val j.isLt occ hocc] at htake
  have hmem := linFirstFree_mem t occ.val (f ⟨j.val, j.isLt⟩).val _ htake
  exact Fin.le_def.mpr hmem.1

theorem linAssign_ne_of_lt (s t : ℕ) (f : Fin s → Fin t)
    (hsucc : LinSuccess s t f) (i j : Fin s) (hlt : i.val < j.val)
    (heq : linAssign s t f hsucc i = linAssign s t f hsucc j) : False := by
  have hi := linAssign_spec s t f hsucc i
  have hj := linAssign_spec s t f hsucc j
  rw [heq] at hi
  have h0i := linOccAux_some_of_le s t f i.val (by omega) hsucc
  obtain ⟨occi, hocci⟩ := linOccAux_eq_some_of_isSome s t f i.val h0i
  rw [linTake_eq s t f i.val i.isLt occi hocci] at hi
  have h1i := linOccAux_some_of_le s t f (i.val + 1) (by omega) hsucc
  obtain ⟨occi', hocci'⟩ := linOccAux_eq_some_of_isSome s t f (i.val + 1) h1i
  have hstep := linOccAux_succ_some s t f i.val occi hocci i.isLt _ hi
  have heq2 : occi'.val = insert (linAssign s t f hsucc j) occi.val := by
    have hcomb := hstep.symm.trans hocci'
    have hsub := Option.some_inj.mp hcomb
    exact (congrArg Subtype.val hsub).symm
  have hmem1 : linAssign s t f hsucc j ∈ occi'.val := by
    rw [heq2]
    exact Finset.mem_insert_self _ _
  have h0j := linOccAux_some_of_le s t f j.val (by omega) hsucc
  obtain ⟨occj, hoccj⟩ := linOccAux_eq_some_of_isSome s t f j.val h0j
  have hsub := linOcc_val_subset s t f (i.val + 1) j.val (by omega) (by omega)
    hsucc occi' occj hocci' hoccj
  have hmem2 : linAssign s t f hsucc j ∈ occj.val := hsub hmem1
  rw [linTake_eq s t f j.val j.isLt occj hoccj] at hj
  have hnot := linFirstFree_mem t occj.val (f ⟨j.val, j.isLt⟩).val _ hj
  exact hnot.2 hmem2

theorem linAssign_injective (s t : ℕ) (f : Fin s → Fin t)
    (hsucc : LinSuccess s t f) :
    Function.Injective (linAssign s t f hsucc) := by
  intro i j heq
  by_contra hne
  rcases lt_trichotomy i.val j.val with h | h | h
  · exact linAssign_ne_of_lt s t f hsucc i j h heq
  · exact hne (Fin.ext h)
  · exact linAssign_ne_of_lt s t f hsucc j i h heq.symm

theorem linUpperSpots_card (t : ℕ) (k : Fin t) :
    (Finset.univ.filter (fun x : Fin t => k.val ≤ x.val)).card = t - k.val := by
  have h1 : Finset.image Fin.val
      (Finset.univ.filter (fun x : Fin t => k.val ≤ x.val)) = Finset.Ico k.val t := by
    ext y
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_Ico]
    constructor
    · rintro ⟨x, hkx, rfl⟩
      exact ⟨hkx, x.isLt⟩
    · rintro ⟨hky, hyt⟩
      exact ⟨⟨y, hyt⟩, hky, rfl⟩
  have h2 : (Finset.image Fin.val
      (Finset.univ.filter (fun x : Fin t => k.val ≤ x.val))).card
      = (Finset.univ.filter (fun x : Fin t => k.val ≤ x.val)).card :=
    Finset.card_image_of_injective _ Fin.val_injective
  rw [h1, Nat.card_Ico] at h2
  omega

theorem linSuccess_imp_threshold (s t : ℕ) (f : Fin s → Fin t)
    (hsucc : LinSuccess s t f) :
    IsPartialParkingFunction s t f := by
  intro k
  have hmaps : ∀ i ∈ Finset.univ.filter (fun i : Fin s => k ≤ f i),
      linAssign s t f hsucc i ∈
        Finset.univ.filter (fun x : Fin t => k.val ≤ x.val) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    have hge := linAssign_ge s t f hsucc i
    have hle : k ≤ linAssign s t f hsucc i := hi.trans hge
    exact Fin.le_def.mp hle
  have hinj : Set.InjOn (linAssign s t f hsucc)
      ↑(Finset.univ.filter (fun i : Fin s => k ≤ f i)) :=
    (linAssign_injective s t f hsucc).injOn
  have hle := Finset.card_le_card_of_injOn
    (linAssign s t f hsucc)
    (fun i hi => hmaps i hi)
    hinj
  rw [linUpperSpots_card t k] at hle
  exact hle

/-- Backward success on a partial path. -/
theorem linOccAux_isSome_of_le (s t : ℕ) (f : Fin s → Fin t) (a b : ℕ)
    (hb : (linOccAux s t f b).isSome) (hab : a ≤ b) :
    (linOccAux s t f a).isSome := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
  clear hab
  induction k with
  | zero =>
    simpa using hb
  | succ k ih =>
    have hbk : a + (k + 1) = (a + k) + 1 := by omega
    have h1 : (linOccAux s t f (a + k)).isSome :=
      linOccAux_some_of_succ s t f (a + k) (hbk ▸ hb)
    exact ih h1

/-- A car parked at or after `c` prefers at or after `c`, provided a free
spot strictly below `c` witnesses minimality. -/
theorem linTake_pref_ge (s t : ℕ) (f : Fin s → Fin t) (j : ℕ) (hj : j < s)
    (x : Fin t) (hx : linTake s t f j hj = some x)
    (occ : { occ : Finset (Fin t) // occ.card ≤ j })
    (hm : linOccAux s t f j = some occ)
    (c : ℕ) (hc : c ≤ x.val) (z : Fin t) (hz : z.val + 1 = c)
    (hzfree : z ∉ occ.val) :
    c ≤ (f ⟨j, hj⟩).val := by
  rw [linTake_eq s t f j hj occ hm] at hx
  by_contra hcon
  have hcon' : (f ⟨j, hj⟩).val < c := by omega
  have h1 : (f ⟨j, hj⟩).val ≤ z.val := by omega
  have hle := linFirstFree_le t occ.val (f ⟨j, hj⟩).val x hx z h1 hzfree
  omega

/-- Partial-path monotonicity with an explicit upper bound. -/
theorem linOcc_val_subset_of_some (s t : ℕ) (f : Fin s → Fin t) (a b : ℕ)
    (oa : { occ : Finset (Fin t) // occ.card ≤ a })
    (ob : { occ : Finset (Fin t) // occ.card ≤ b })
    (ha : linOccAux s t f a = some oa) (hb : linOccAux s t f b = some ob)
    (hab : a ≤ b) (hbs : b ≤ s) : oa.val ⊆ ob.val := by
  exact Nat.le_induction
    (P := fun m _ => m ≤ b →
      ∀ om : { occ : Finset (Fin t) // occ.card ≤ m },
        linOccAux s t f m = some om → oa.val ⊆ om.val)
    (fun _ om hom => by
      have e := Option.some_inj.mp (ha.symm.trans hom)
      subst e
      exact Finset.Subset.rfl)
    (fun m _ ih hmb om' hom' => by
      have hms : m < s := by omega
      have hprev : (linOccAux s t f m).isSome :=
        linOccAux_some_of_succ s t f m (hom'.symm ▸ Option.isSome_some)
      obtain ⟨om0, hom0⟩ := Option.isSome_iff_exists.mp hprev
      exact Finset.Subset.trans (ih (by omega) om0 hom0)
        (linOcc_val_subset_step s t f m hms om0 om' hom0 hom'))
    b hab (le_refl b) ob hb

/-- The occupied set is the image of the chosen takes. -/
theorem linOcc_image (s t : ℕ) (f : Fin s → Fin t) (n : ℕ) (hn : n < s)
    (car : ∀ j : ℕ, j < n → Fin t)
    (hcar : ∀ j (hj : j < n),
      linTake s t f j (Nat.lt_trans hj hn) = some (car j hj))
    (_tpos : 0 < t) (F : Fin s → Fin t)
    (hF : ∀ i : Fin s, ∀ h : i.val < n, F i = car i.val h) :
    ∀ m : ℕ, ∀ _hmn : m ≤ n, ∀ om : { occ : Finset (Fin t) // occ.card ≤ m },
      linOccAux s t f m = some om →
      om.val = (Finset.univ.filter (fun i : Fin s => i.val < m)).image F := by
  intro m
  induction m with
  | zero =>
    intro hmn om hom
    have hempty : Finset.univ.filter (fun i : Fin s => i.val < 0) = ∅ :=
      Finset.eq_empty_of_forall_notMem (by
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        omega)
    have h0 : linOccAux s t f 0 =
        some (⟨∅, by simp⟩ : { occ : Finset (Fin t) // occ.card ≤ 0 }) := rfl
    have hom0 : (⟨∅, by simp⟩ : { occ : Finset (Fin t) // occ.card ≤ 0 }) = om :=
      Option.some_inj.mp (h0.symm.trans hom)
    have hval : om.val = ∅ := (congrArg Subtype.val hom0).symm
    rw [hempty, Finset.image_empty, hval]
  | succ m ih =>
    intro hmn om hom
    have hms : m < s := lt_of_le_of_lt (by omega) hn
    have hmltn : m < n := by omega
    have hprev := linOccAux_isSome_of_le s t f m (m + 1)
      (hom.symm ▸ Option.isSome_some) (Nat.le_succ m)
    obtain ⟨oprev, hprev'⟩ := Option.isSome_iff_exists.mp hprev
    have ih' := ih (by omega) oprev hprev'
    have htake : linFirstFree t oprev.val (f ⟨m, hms⟩).val = some (car m hmltn) := by
      have h1 := hcar m hmltn
      rw [linTake_eq s t f m _ oprev hprev'] at h1
      exact h1
    have hsucc := linOccAux_succ_some s t f m oprev hprev' hms (car m hmltn) htake
    have hval_eq : om.val = (⟨insert (car m hmltn) oprev.val, by
        have hle := oprev.property
        have hci := Finset.card_insert_le (car m hmltn) oprev.val
        omega⟩ : { occ : Finset (Fin t) // occ.card ≤ m + 1 }).val :=
      congrArg Subtype.val (Option.some_inj.mp (hom.symm.trans hsucc))
    have hfilter : Finset.univ.filter (fun i : Fin s => i.val < m + 1) =
        insert ⟨m, hms⟩ (Finset.univ.filter (fun i : Fin s => i.val < m)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert]
      constructor
      · intro hi
        by_cases h : i.val < m
        · exact Or.inr h
        · left
          have hiv : i.val = m := by omega
          exact Fin.ext hiv
      · rintro (rfl | h)
        · change m < m + 1
          exact Nat.lt_succ_self m
        · omega
    rw [hval_eq]
    change insert (car m hmltn) oprev.val =
      (Finset.univ.filter (fun i : Fin s => i.val < m + 1)).image F
    rw [hfilter, Finset.image_insert, ← ih', hF ⟨m, hms⟩ hmltn]

/-- Threshold implies greedy success, via the cluster argument. -/
theorem threshold_imp_linSuccess (s t : ℕ) (f : Fin s → Fin t)
    (h : IsPartialParkingFunction s t f) (_hst : s ≤ t) :
    LinSuccess s t f := by
  by_contra hfail
  have hnone : linOccAux s t f s = none :=
    Option.not_isSome_iff_eq_none.mp hfail
  -- First failure triple.
  have triple : ∃ n : ℕ, ∃ _ : n < s, ∃ occ : { occ : Finset (Fin t) // occ.card ≤ n },
      linOccAux s t f n = some occ ∧
        linFirstFree t occ.val (f ⟨n, ‹n < s›⟩).val = none := by
    by_contra hcon
    simp only [not_exists, not_and] at hcon
    have hall : ∀ m : ℕ, m ≤ s → (linOccAux s t f m).isSome := by
      intro m hm
      induction m with
      | zero =>
        rw [linOccAux_zero]
        exact Option.isSome_some
      | succ m ih =>
        have hms : m ≤ s := by omega
        have ih' := ih hms
        obtain ⟨occ, hocc⟩ := Option.isSome_iff_exists.mp ih'
        have hms' : m < s := by omega
        obtain ⟨x, hx⟩ := Option.ne_none_iff_exists.mp (hcon m hms' occ hocc)
        rw [linOccAux_succ_some s t f m occ hocc hms' x hx.symm]
        exact Option.isSome_some
    have hs := hall s (le_refl s)
    rw [hnone] at hs
    simp at hs
  obtain ⟨n, hn, occ, hm, hff⟩ := triple
  -- Every spot at or after the failed preference is occupied.
  have allocc : ∀ y : Fin t, (f ⟨n, hn⟩).val ≤ y.val → y ∈ occ.val :=
    fun y hy => linFirstFree_none t occ.val _ hff y hy
  -- The cluster base: least `c` with `[c, t)` fully occupied.
  have hex : ∃ c : ℕ, ∀ y : Fin t, c ≤ y.val → y ∈ occ.val := by
    refine ⟨t, fun y hy => absurd hy (by have := y.isLt; omega)⟩
  have : DecidablePred (fun c : ℕ => ∀ y : Fin t, c ≤ y.val → y ∈ occ.val) :=
    fun c => inferInstance
  set cstar := Nat.find hex with hcstar
  have hPstar : ∀ y : Fin t, cstar ≤ y.val → y ∈ occ.val :=
    Nat.find_spec hex
  have hlea : cstar ≤ (f ⟨n, hn⟩).val :=
    Nat.find_min' hex allocc
  have hlt : cstar < t :=
    lt_of_le_of_lt hlea (f ⟨n, hn⟩).isLt
  -- A free spot at `cstar - 1` (unless `cstar = 0`).
  have hfree : cstar = 0 ∨ ∃ z : Fin t, z.val + 1 = cstar ∧ z ∉ occ.val := by
    by_cases hc0 : cstar = 0
    · exact Or.inl hc0
    · right
      have hpos : 0 < cstar := Nat.pos_of_ne_zero hc0
      have hmin := Nat.find_min hex (show cstar - 1 < cstar by omega)
      rw [not_forall] at hmin
      obtain ⟨y, hy⟩ := hmin
      obtain ⟨hle_y, hfree_y⟩ := not_imp.mp hy
      have hylt : y.val < cstar :=
        lt_of_not_ge (fun hcon => hfree_y (hPstar y hcon))
      have hyeq : y.val + 1 = cstar := by omega
      exact ⟨y, hyeq, hfree_y⟩
  -- Takes succeed for every earlier car.
  have take_some : ∀ j : ℕ, ∀ hj : j < n, ∃ x : Fin t,
      linTake s t f j (Nat.lt_trans hj hn) = some x := by
    intro j hj
    have hjn : j < s := Nat.lt_trans hj hn
    have hjs := linOccAux_isSome_of_le s t f j n (hm.symm ▸ Option.isSome_some)
      (Nat.le_of_lt hj)
    obtain ⟨oj, hoj⟩ := Option.isSome_iff_exists.mp hjs
    match hffj : linFirstFree t oj.val (f ⟨j, hjn⟩).val with
    | none =>
      exfalso
      have hsucc := linOccAux_succ_none_take s t f j oj hoj hjn hffj
      have hnone2 := linOccAux_none_of_le s t f (j + 1) n (by omega) hsucc
      rw [hm] at hnone2
      simp at hnone2
    | some x =>
      exact ⟨x, by
        have hbase : linTake s t f j (Nat.lt_trans hj hn) =
            linFirstFree t oj.val (f ⟨j, hjn⟩).val := by
          unfold linTake
          rw [hoj]
        rw [hbase, hffj]⟩
  -- The chosen car for each earlier index.
  choose car hcar using take_some
  have tpos : 0 < t := by omega
  set carAll : Fin s → Fin t :=
    fun i => if h : i.val < n then car i.val h else (⟨0, tpos⟩ : Fin t) with hcarAlldef
  have hcarAll : ∀ i : Fin s, ∀ h : i.val < n, carAll i = car i.val h :=
    fun i h => dite_eq_left h
  have htakeAll : ∀ i : Fin s, ∀ h : i.val < n,
      linTake s t f i.val (Nat.lt_trans h hn) = some (carAll i) := by
    intro i h
    rw [hcarAll i h]
    exact hcar i.val h
  have himg : occ.val = (Finset.univ.filter (fun i : Fin s => i.val < n)).image carAll :=
    linOcc_image s t f n hn car hcar tpos carAll hcarAll n (le_refl n) occ hm
  -- The cluster threshold and its spots.
  set k : Fin t := ⟨cstar, hlt⟩ with hkdef
  have hkval : k.val = cstar := rfl
  have hth := h k
  rw [hkval] at hth
  set Spots : Finset (Fin t) :=
    Finset.univ.filter (fun y : Fin t => cstar ≤ y.val) with hSpotsdef
  have hspots : Spots.card = t - cstar := linUpperSpots_card t ⟨cstar, hlt⟩
  -- Every cluster spot is taken by an earlier car preferring at/after `cstar`.
  have ycar : ∀ y : Fin t, y ∈ Spots → ∃ i : Fin s,
      i.val < n ∧ carAll i = y ∧ k ≤ f i := by
    intro y hy
    simp only [hSpotsdef, Finset.mem_filter, Finset.mem_univ, true_and] at hy
    have hyocc : y ∈ occ.val := hPstar y hy
    rw [himg] at hyocc
    rw [Finset.mem_image] at hyocc
    obtain ⟨i, hi_mem, hi_eq⟩ := hyocc
    have himem' : i.val < n := (Finset.mem_filter.mp hi_mem).2
    have htake : linTake s t f i.val (Nat.lt_trans himem' hn) = some y := by
      have h1 := htakeAll i himem'
      rwa [hi_eq] at h1
    have hOj := linOccAux_isSome_of_le s t f i.val n
      (hm.symm ▸ Option.isSome_some) (Nat.le_of_lt himem')
    obtain ⟨oj, hoj⟩ := Option.isSome_iff_exists.mp hOj
    have hsuboj := linOcc_val_subset_of_some s t f i.val n oj occ hoj hm
      (Nat.le_of_lt himem') (Nat.le_of_lt hn)
    have hpref : k ≤ f i := by
      rcases hfree with hc0 | ⟨z, hz, hzfree⟩
      · have hk0 : k.val = 0 := hc0
        have h0 : (0 : ℕ) ≤ (f i).val := Nat.zero_le _
        rw [← hk0] at h0
        exact Fin.le_def.mpr h0
      · have hzfree' : z ∉ oj.val := fun hmem => hzfree (hsuboj hmem)
        have hle := linTake_pref_ge s t f i.val _ y htake oj hoj cstar hy z hz hzfree'
        exact Fin.le_def.mpr hle
    exact ⟨i, himem', hi_eq, hpref⟩
  choose icar hicarn hicar_eq hicar_pref using ycar
  -- The witnessing cars, plus the failed car, violate the threshold.
  set Cars0 : Finset (Fin s) :=
    Spots.attach.image (fun y => icar y.val y.property) with hCars0def
  have hinj0 : Function.Injective
      (fun y : ↥Spots => icar y.val y.property) := by
    intro a b hab
    simp only at hab
    have e1 := hicar_eq a.val a.property
    have e2 := hicar_eq b.val b.property
    have hval : a.val = b.val := by rw [← e1, ← e2, hab]
    exact Subtype.ext hval
  have hcard0 : Cars0.card = Spots.card := by
    rw [hCars0def, Finset.card_image_of_injective _ hinj0, Finset.card_attach]
  have hsub0 : Cars0 ⊆ Finset.univ.filter (fun i : Fin s => k ≤ f i) := by
    intro i hi
    rw [hCars0def, Finset.mem_image] at hi
    obtain ⟨y, _, rfl⟩ := hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hicar_pref y.val y.property
  set Cars : Finset (Fin s) := insert ⟨n, hn⟩ Cars0 with hCarsdef
  have hnotin : (⟨n, hn⟩ : Fin s) ∉ Cars0 := by
    intro hmem
    rw [hCars0def, Finset.mem_image] at hmem
    obtain ⟨y, _, hy⟩ := hmem
    have hlt_y := hicarn y.val y.property
    rw [hy] at hlt_y
    simp at hlt_y
  have hcardCars : Cars.card = t - cstar + 1 := by
    rw [hCarsdef, Finset.card_insert_of_notMem hnotin, hcard0, hspots]
  have hsub : Cars ⊆ Finset.univ.filter (fun i : Fin s => k ≤ f i) := by
    intro i hi
    rw [hCarsdef, Finset.mem_insert] at hi
    rcases hi with rfl | h
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact Fin.le_def.mpr hlea
    · exact hsub0 h
  have hle := Finset.card_le_card hsub
  rw [hcardCars] at hle
  omega

end MetaMathlibExt.PollakPartialParking
