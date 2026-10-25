/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean -/

import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Data.Nat.Fib.Basic
import Def.NumberTheory.PellNumberSequence
import Mathlib.Tactic.Ring
import Def.Combinatorics.Enumerative.W4PathDominoTilings.Part13
open SimpleGraph


section

namespace MetaMathlibExt

theorem partner_bwd_eq (m : ℕ) (t : Tiling m ∅) (v : Fin 4 × Fin m) :
    partner m (bwdSubgraph m t) (bwdSubgraph_perfect m t) v = partnerT m t v := by
  have hAdj : (bwdSubgraph m t).Adj v (partnerT m t v) := rfl
  have huniq := partner_unique m (bwdSubgraph m t) (bwdSubgraph_perfect m t) v
    (partnerT m t v) hAdj
  exact huniq.symm

theorem getS_build_eq (m : ℕ) (M : (W4 □ pathGraph m).Subgraph)
    (hM : M.IsPerfectMatching) : ∀ (k : ℕ) (hk : k ≤ m) (j : ℕ) (_hj : j < k),
    getS k (topHoles m M hM k) (buildTiling m M hM k hk) j = vertSet m M hM j := by
  intro k
  induction k with
  | zero =>
    intro hk j hj
    exact absurd hj (Nat.not_lt_zero j)
  | succ k ih =>
    intro hk j _hj
    by_cases hjm : j = k
    · rw [hjm]
      have htop : getS (k + 1) (topHoles m M hM (k + 1))
          (buildTiling m M hM (k + 1) hk) k = topHoles m M hM (k + 1) := by
        have := getS_top k (topHoles m M hM (k + 1)) (buildTiling m M hM (k + 1) hk)
        exact this
      rw [htop]
      rfl
    · have hjk : j < k := by omega
      have hk' : k ≤ m := by omega
      have hrec : getS (k + 1) (topHoles m M hM (k + 1))
          (buildTiling m M hM (k + 1) hk) j =
          getS k ((buildTiling m M hM (k + 1) hk).1)
            ((buildTiling m M hM (k + 1) hk).2.2.1) j :=
        getS_recurse k _ _ j hjm
      rw [hrec]
      exact ih hk' j hjk

theorem vertSet_bwd_eq (m : ℕ) (t : Tiling m ∅) (j : ℕ) :
    vertSet m (bwdSubgraph m t) (bwdSubgraph_perfect m t) j = getS m ∅ t j := by
  ext a
  rw [vertSet_mem]
  constructor
  · rintro ⟨i, k, hi, hk, heq⟩
    have hpeq := partner_bwd_eq m t (a, i)
    rw [hpeq] at heq
    have hjlt : j < m := by omega
    have hup : a ∈ getS m ∅ t j := by
      have h2 : (partnerT m t (a, i)).2 = k := congrArg Prod.snd heq
      have hkval : k.val = j + 1 := hk
      have hival : i.val = j := hi
      have hpval : (partnerT m t (a, i)).2.val = j + 1 := by
        rw [h2, hkval]
      by_cases hmem : a ∈ getS m ∅ t i.val
      · have : i.val = j := hival
        rw [this] at hmem
        exact hmem
      · by_cases hdown : a ∈ (if i.val = 0 then ∅ else getS m ∅ t (i.val - 1))
        · have hpd := partnerT_down m t a i hmem hdown
          have : (partnerT m t (a, i)).2.val + 1 = i.val := hpd.2
          omega
        · have hhor := partnerT_horiz m t a i hmem hdown
          have : (partnerT m t (a, i)).2 = i := congrArg Prod.snd hhor
          have : (partnerT m t (a, i)).2.val = i.val := congrArg Fin.val this
          omega
    exact hup
  · intro hmem
    have hjlt : j < m := by
      by_contra hcon
      have hle : m ≤ j := by omega
      have hempty : getS m ∅ t j = ∅ := getS_out_empty m ∅ t j hle
      rw [hempty] at hmem
      exact absurd hmem (Finset.notMem_empty a)
    have hj1 : j + 1 < m := mem_above_up_lt m t j hjlt a hmem
    refine ⟨⟨j, hjlt⟩, ⟨j + 1, hj1⟩, rfl, rfl, ?_⟩
    have hpeq := partner_bwd_eq m t (a, ⟨j, hjlt⟩)
    rw [hpeq]
    have hpu := partnerT_up m t a ⟨j, hjlt⟩ hmem
    have h1 : (partnerT m t (a, ⟨j, hjlt⟩)).1 = a := hpu.1
    have h2 : (partnerT m t (a, ⟨j, hjlt⟩)).2.val = j + 1 := hpu.2
    have h3 : (partnerT m t (a, ⟨j, hjlt⟩)).2 = (⟨j + 1, hj1⟩ : Fin m) := Fin.ext h2
    exact Prod.ext h1 h3

theorem tiling_ext_of_getSF_eq (m : ℕ) (S' : Finset (Fin 4))
    (t1 t2 : Tiling m S')
    (hS : ∀ j, j < m → getS m S' t1 j = getS m S' t2 j)
    (hF : ∀ j, j < m → getF m S' t1 j = getF m S' t2 j) :
    t1 = t2 := by
  induction m generalizing S' with
  | zero =>
    cases t1
    cases t2
    rfl
  | succ m ih =>
    obtain ⟨S1, hd1, tm1, h1⟩ := t1
    obtain ⟨S2, hd2, tm2, h2⟩ := t2
    cases m with
    | zero =>
      have e1 : S1 = ∅ := tm1.down
      have e2 : S2 = ∅ := tm2.down
      have hSeq : S1 = S2 := e1.trans e2.symm
      subst hSeq
      have htm : tm1 = tm2 := by
        cases tm1
        cases tm2
        rfl
      subst htm
      have eF := hF 0 (by omega)
      have g1 : getF (0 + 1) S' ⟨S1, hd1, tm1, h1⟩ 0 = h1.val :=
        getF_top 0 S' _
      have g2 : getF (0 + 1) S' ⟨S1, hd2, tm1, h2⟩ 0 = h2.val :=
        getF_top 0 S' _
      have hval : h1.val = h2.val := g1.symm.trans (eF.trans g2)
      have hh : h1 = h2 := Subtype.ext hval
      subst hh
      have hhd : hd1 = hd2 := by
        cases hd1
        cases hd2
        rfl
      cases hhd
      rfl
    | succ m' =>
      have eS := hS m' (by omega)
      have r1 : getS ((m' + 1) + 1) S' ⟨S1, hd1, tm1, h1⟩ m' =
          getS (m' + 1) S1 tm1 m' :=
        getS_recurse (m' + 1) S' _ m' (by omega)
      have r2 : getS ((m' + 1) + 1) S' ⟨S2, hd2, tm2, h2⟩ m' =
          getS (m' + 1) S2 tm2 m' :=
        getS_recurse (m' + 1) S' _ m' (by omega)
      have t1 : getS (m' + 1) S1 tm1 m' = S1 := getS_top m' S1 tm1
      have t2 : getS (m' + 1) S2 tm2 m' = S2 := getS_top m' S2 tm2
      have hSeq : S1 = S2 := t1.symm.trans (r1.symm.trans (eS.trans (r2.trans t2)))
      subst hSeq
      have hS' : ∀ j, j < m' + 1 →
          getS (m' + 1) S1 tm1 j = getS (m' + 1) S1 tm2 j := by
        intro j hj
        have e := hS j (by omega)
        have rr1 : getS ((m' + 1) + 1) S' ⟨S1, hd1, tm1, h1⟩ j =
            getS (m' + 1) S1 tm1 j :=
          getS_recurse (m' + 1) S' _ j (by omega)
        have rr2 : getS ((m' + 1) + 1) S' ⟨S1, hd2, tm2, h2⟩ j =
            getS (m' + 1) S1 tm2 j :=
          getS_recurse (m' + 1) S' _ j (by omega)
        exact rr1.symm.trans (e.trans rr2)
      have hF' : ∀ j, j < m' + 1 →
          getF (m' + 1) S1 tm1 j = getF (m' + 1) S1 tm2 j := by
        intro j hj
        have e := hF j (by omega)
        have rr1 : getF ((m' + 1) + 1) S' ⟨S1, hd1, tm1, h1⟩ j =
            getF (m' + 1) S1 tm1 j :=
          getF_recurse (m' + 1) S' _ j (by omega)
        have rr2 : getF ((m' + 1) + 1) S' ⟨S1, hd2, tm2, h2⟩ j =
            getF (m' + 1) S1 tm2 j :=
          getF_recurse (m' + 1) S' _ j (by omega)
        exact rr1.symm.trans (e.trans rr2)
      have htm : tm1 = tm2 := ih S1 tm1 tm2 hS' hF'
      subst htm
      have eF := hF (m' + 1) (by omega)
      have g1 : getF ((m' + 1) + 1) S' ⟨S1, hd1, tm1, h1⟩ (m' + 1) = h1.val :=
        getF_top (m' + 1) S' _
      have g2 : getF ((m' + 1) + 1) S' ⟨S1, hd2, tm1, h2⟩ (m' + 1) = h2.val :=
        getF_top (m' + 1) S' _
      have hval : h1.val = h2.val := g1.symm.trans (eF.trans g2)
      have hh : h1 = h2 := Subtype.ext hval
      subst hh
      have hhd : hd1 = hd2 := by
        cases hd1
        cases hd2
        rfl
      cases hhd
      rfl

theorem horizFunNat_bwd_eq (m : ℕ) (t : Tiling m ∅) (j : ℕ) (hj : j < m)
    (a : Fin 4) :
    horizFunNat m (bwdSubgraph m t) (bwdSubgraph_perfect m t) j a =
      getF m ∅ t j a := by
  rw [horizFunNat_eq m _ _ j hj a]
  have hpeq := partner_bwd_eq m t (a, ⟨j, hj⟩)
  by_cases h_up : a ∈ getS m ∅ t j
  · have hpu := partnerT_up m t a ⟨j, hj⟩ h_up
    have hne : (partner m (bwdSubgraph m t) (bwdSubgraph_perfect m t)
        (a, ⟨j, hj⟩)).2 ≠ ⟨j, hj⟩ := by
      rw [hpeq]
      intro hcon
      have hval : (partnerT m t (a, ⟨j, hj⟩)).2.val = j :=
        congrArg Fin.val hcon
      omega
    rw [ite_eq_right hne]
    have hprops := (tiling_props m ∅ t j hj).2
    have hmemU : a ∈ ((if j = 0 then ∅ else getS m ∅ t (j - 1)) ∪
        getS m ∅ t j) :=
      Finset.mem_union_right _ h_up
    have hU : a ∉ Finset.univ \ ((if j = 0 then ∅ else getS m ∅ t (j - 1)) ∪
        getS m ∅ t j) := by
      intro hcon
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hcon
      exact hcon hmemU
    have hfa : getF m ∅ t j a = a := hprops.2 a hU
    exact hfa.symm
  · by_cases h_down : a ∈ (if j = 0 then ∅ else getS m ∅ t (j - 1))
    · have hpd := partnerT_down m t a ⟨j, hj⟩ h_up h_down
      have hne : (partner m (bwdSubgraph m t) (bwdSubgraph_perfect m t)
          (a, ⟨j, hj⟩)).2 ≠ ⟨j, hj⟩ := by
        rw [hpeq]
        intro hcon
        have hval : (partnerT m t (a, ⟨j, hj⟩)).2.val = j :=
          congrArg Fin.val hcon
        omega
      rw [ite_eq_right hne]
      have hprops := (tiling_props m ∅ t j hj).2
      have hmemU : a ∈ ((if j = 0 then ∅ else getS m ∅ t (j - 1)) ∪
          getS m ∅ t j) :=
        Finset.mem_union_left _ h_down
      have hU : a ∉ Finset.univ \ ((if j = 0 then ∅ else getS m ∅ t (j - 1)) ∪
          getS m ∅ t j) := by
        intro hcon
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hcon
        exact hcon hmemU
      have hfa : getF m ∅ t j a = a := hprops.2 a hU
      exact hfa.symm
    · have hhor := partnerT_horiz m t a ⟨j, hj⟩ h_up h_down
      have h2 : (partnerT m t (a, ⟨j, hj⟩)).2 = ⟨j, hj⟩ :=
        congrArg Prod.snd hhor
      have hsame : (partner m (bwdSubgraph m t) (bwdSubgraph_perfect m t)
          (a, ⟨j, hj⟩)).2 = ⟨j, hj⟩ := by
        rw [hpeq, h2]
      rw [ite_eq_left hsame]
      rw [hpeq, hhor]

theorem fwd_bwd_eq (m : ℕ) (t : Tiling m ∅) :
    fwdTiling m (bwdSubgraph m t) (bwdSubgraph_perfect m t) = t := by
  apply tiling_ext_of_getSF_eq
  · intro j hj
    cases m with
    | zero => exact absurd hj (Nat.not_lt_zero j)
    | succ m' =>
      have htop : topHoles (m' + 1) (bwdSubgraph (m' + 1) t)
          (bwdSubgraph_perfect (m' + 1) t) (m' + 1) = ∅ := by
        change vertSet (m' + 1) _ _ m' = ∅
        apply vertSet_top_empty
        omega
      have hfwd : fwdTiling (m' + 1) (bwdSubgraph (m' + 1) t)
          (bwdSubgraph_perfect (m' + 1) t) =
          htop.rec (buildTiling (m' + 1) (bwdSubgraph (m' + 1) t)
            (bwdSubgraph_perfect (m' + 1) t) (m' + 1) (by omega)) := rfl
      rw [hfwd, getS_rec_eq]
      have hbuild := getS_build_eq (m' + 1) (bwdSubgraph (m' + 1) t)
        (bwdSubgraph_perfect (m' + 1) t) (m' + 1) (by omega) j hj
      rw [hbuild]
      exact vertSet_bwd_eq (m' + 1) t j
  · intro j hj
    cases m with
    | zero => exact absurd hj (Nat.not_lt_zero j)
    | succ m' =>
      have htop : topHoles (m' + 1) (bwdSubgraph (m' + 1) t)
          (bwdSubgraph_perfect (m' + 1) t) (m' + 1) = ∅ := by
        change vertSet (m' + 1) _ _ m' = ∅
        apply vertSet_top_empty
        omega
      have hfwd : fwdTiling (m' + 1) (bwdSubgraph (m' + 1) t)
          (bwdSubgraph_perfect (m' + 1) t) =
          htop.rec (buildTiling (m' + 1) (bwdSubgraph (m' + 1) t)
            (bwdSubgraph_perfect (m' + 1) t) (m' + 1) (by omega)) := rfl
      rw [hfwd, getF_rec_eq]
      have hbuild := getF_build_eq (m' + 1) (bwdSubgraph (m' + 1) t)
        (bwdSubgraph_perfect (m' + 1) t) (m' + 1) (by omega) j hj
      rw [hbuild]
      funext a
      exact horizFunNat_bwd_eq (m' + 1) t j hj a

theorem getS_fwd_eq (m : ℕ) (M : (W4 □ pathGraph m).Subgraph)
    (hM : M.IsPerfectMatching) (j : ℕ) (hj : j < m) :
    getS m ∅ (fwdTiling m M hM) j = vertSet m M hM j := by
  cases m with
  | zero => exact absurd hj (Nat.not_lt_zero j)
  | succ m' =>
    have htop : topHoles (m' + 1) M hM (m' + 1) = ∅ := by
      change vertSet (m' + 1) _ _ m' = ∅
      apply vertSet_top_empty
      omega
    have hfwd : fwdTiling (m' + 1) M hM =
        htop.rec (buildTiling (m' + 1) M hM (m' + 1) (by omega)) := rfl
    rw [hfwd, getS_rec_eq]
    exact getS_build_eq (m' + 1) M hM (m' + 1) (by omega) j hj

theorem getF_fwd_eq (m : ℕ) (M : (W4 □ pathGraph m).Subgraph)
    (hM : M.IsPerfectMatching) (j : ℕ) (hj : j < m) :
    getF m ∅ (fwdTiling m M hM) j = horizFunNat m M hM j := by
  cases m with
  | zero => exact absurd hj (Nat.not_lt_zero j)
  | succ m' =>
    have htop : topHoles (m' + 1) M hM (m' + 1) = ∅ := by
      change vertSet (m' + 1) _ _ m' = ∅
      apply vertSet_top_empty
      omega
    have hfwd : fwdTiling (m' + 1) M hM =
        htop.rec (buildTiling (m' + 1) M hM (m' + 1) (by omega)) := rfl
    rw [hfwd, getF_rec_eq]
    exact getF_build_eq (m' + 1) M hM (m' + 1) (by omega) j hj

theorem partnerT_fwd_eq (m : ℕ) (M : (W4 □ pathGraph m).Subgraph)
    (hM : M.IsPerfectMatching) (v : Fin 4 × Fin m) :
    partnerT m (fwdTiling m M hM) v = partner m M hM v := by
  obtain ⟨a, i⟩ := v
  have hj : i.val < m := i.isLt
  by_cases hsame : (partner m M hM (a, i)).2 = i
  · have hUp : a ∉ getS m ∅ (fwdTiling m M hM) i.val := by
      intro hcon
      rw [getS_fwd_eq m M hM i.val hj] at hcon
      have hmem : a ∈ aboveSet m M hM i.val := hcon
      obtain ⟨k, hk, heq⟩ := above_mem_up m M hM i.val hj a hmem
      have hi : (⟨i.val, hj⟩ : Fin m) = i := Fin.ext rfl
      have h1 : (partner m M hM (a, i)).2 = k := by
        have h := congrArg Prod.snd heq
        rw [hi] at h
        exact h
      have hkk : k = i := h1.symm.trans hsame
      have hval : k.val = i.val := congrArg Fin.val hkk
      omega
    have hDown : a ∉ (if i.val = 0 then ∅ else
        getS m ∅ (fwdTiling m M hM) (i.val - 1)) := by
      by_cases hj0 : i.val = 0
      · simp only [ite_eq_left hj0]
        exact Finset.notMem_empty a
      · simp only [ite_eq_right hj0]
        intro hcon
        have hj1 : i.val - 1 < m := by omega
        rw [getS_fwd_eq m M hM (i.val - 1) hj1] at hcon
        rw [vertSet_mem] at hcon
        obtain ⟨i', k', hi', hk', heq⟩ := hcon
        have hkk' : k' = i := by
          apply Fin.ext
          omega
        have hsym := partner_pair_symm m M hM a i' k' heq
        rw [hkk'] at hsym
        have h2 : (partner m M hM (a, i)).2 = i' := congrArg Prod.snd hsym
        rw [hsame] at h2
        have hval : i.val = i'.val := congrArg Fin.val h2
        omega
    have hhor := partnerT_horiz m (fwdTiling m M hM) a i hUp hDown
    have hF := getF_fwd_eq m M hM i.val hj
    have hmem : a ∈ leftoverSet m M hM i.val := by
      rw [leftover_mem]
      intro hcon
      rw [Finset.mem_union] at hcon
      rcases hcon with hb | ha
      · by_cases hj0 : i.val = 0
        · have hbs : belowSet m M hM i.val = ∅ := by rw [hj0]; rfl
          rw [hbs] at hb
          exact (Finset.notMem_empty a) hb
        · have hj1 : i.val - 1 < m := by omega
          have hbs : belowSet m M hM i.val = vertSet m M hM (i.val - 1) := by
            obtain ⟨j', hj'⟩ := Nat.exists_eq_succ_of_ne_zero hj0
            rw [hj']
            rfl
          rw [hbs] at hb
          have hget := getS_fwd_eq m M hM (i.val - 1) hj1
          simp only [ite_eq_right hj0] at hDown
          rw [hget] at hDown
          exact hDown hb
      · have hget := getS_fwd_eq m M hM i.val hj
        rw [hget] at hUp
        exact hUp ha
    have hfa : horizFunNat m M hM i.val a = (partner m M hM (a, i)).1 := by
      have hi : (⟨i.val, hj⟩ : Fin m) = i := Fin.ext rfl
      have h := horizFunNat_of_mem m M hM i.val hj a hmem
      rw [hi] at h
      exact h
    rw [hhor]
    have hFa : getF m ∅ (fwdTiling m M hM) i.val a =
        horizFunNat m M hM i.val a :=
      congrFun hF a
    rw [hFa, hfa]
    exact Prod.ext rfl hsame.symm
  · have ⟨haeq, hpath⟩ := partner_ne_layer_vert m M hM a i hsame
    rw [pathGraph_adj] at hpath
    rcases hpath with hup | hdown
    · have hmemV : a ∈ vertSet m M hM i.val := by
        rw [vertSet_mem]
        refine ⟨i, (partner m M hM (a, i)).2, rfl, hup.symm, ?_⟩
        exact Prod.ext haeq rfl
      have hmemG : a ∈ getS m ∅ (fwdTiling m M hM) i.val := by
        rw [getS_fwd_eq m M hM i.val hj]
        exact hmemV
      have hpu := partnerT_up m (fwdTiling m M hM) a i hmemG
      have h1 : (partnerT m (fwdTiling m M hM) (a, i)).1 = a := hpu.1
      have h2 : (partnerT m (fwdTiling m M hM) (a, i)).2 =
          (partner m M hM (a, i)).2 := by
        apply Fin.ext
        have hval : (partnerT m (fwdTiling m M hM) (a, i)).2.val =
            i.val + 1 := hpu.2
        omega
      exact Prod.ext (h1.trans haeq.symm) h2
    · have hj0 : i.val ≠ 0 := by omega
      have hUp : a ∉ getS m ∅ (fwdTiling m M hM) i.val := by
        intro hcon
        rw [getS_fwd_eq m M hM i.val hj] at hcon
        have hmem : a ∈ aboveSet m M hM i.val := hcon
        obtain ⟨k, hk, heq⟩ := above_mem_up m M hM i.val hj a hmem
        have hi : (⟨i.val, hj⟩ : Fin m) = i := Fin.ext rfl
        have h1 : (partner m M hM (a, i)).2 = k := by
          have h := congrArg Prod.snd heq
          rw [hi] at h
          exact h
        have hval : (partner m M hM (a, i)).2.val = k.val :=
          congrArg Fin.val h1
        omega
      have hDown : a ∈ (if i.val = 0 then ∅ else
          getS m ∅ (fwdTiling m M hM) (i.val - 1)) := by
        simp only [ite_eq_right hj0]
        have hj1 : i.val - 1 < m := by omega
        rw [getS_fwd_eq m M hM (i.val - 1) hj1]
        rw [vertSet_mem]
        have hpeq : partner m M hM (a, i) =
            (a, (partner m M hM (a, i)).2) :=
          Prod.ext haeq rfl
        have hsym := partner_pair_symm m M hM a i
          (partner m M hM (a, i)).2 hpeq
        refine ⟨(partner m M hM (a, i)).2, i, by omega, by omega, hsym⟩
      have hpd := partnerT_down m (fwdTiling m M hM) a i hUp hDown
      have h1 : (partnerT m (fwdTiling m M hM) (a, i)).1 = a := hpd.1
      have h2 : (partnerT m (fwdTiling m M hM) (a, i)).2 =
          (partner m M hM (a, i)).2 := by
        apply Fin.ext
        have hval : (partnerT m (fwdTiling m M hM) (a, i)).2.val + 1 =
            i.val := hpd.2
        omega
      exact Prod.ext (h1.trans haeq.symm) h2

theorem bwd_fwd_eq (m : ℕ) (M : (W4 □ pathGraph m).Subgraph)
    (hM : M.IsPerfectMatching) :
    bwdSubgraph m (fwdTiling m M hM) = M := by
  have hMverts : M.verts = Set.univ := by
    apply Set.eq_univ_of_forall
    intro v
    exact M.edge_vert (partner_spec m M hM v)
  have hverts : (bwdSubgraph m (fwdTiling m M hM)).verts = M.verts := by
    have hbwd : (bwdSubgraph m (fwdTiling m M hM)).verts = Set.univ := rfl
    rw [hbwd, hMverts]
  have hAdj : ∀ v w, (bwdSubgraph m (fwdTiling m M hM)).Adj v w ↔ M.Adj v w := by
    intro v w
    have hPT := partnerT_fwd_eq m M hM v
    constructor
    · intro h
      have heq : w = partnerT m (fwdTiling m M hM) v := h
      rw [hPT] at heq
      rw [heq]
      exact partner_spec m M hM v
    · intro h
      have heq : w = partner m M hM v := partner_unique m M hM v w h
      have h2 : w = partnerT m (fwdTiling m M hM) v := heq.trans hPT.symm
      exact h2
  have hAdjEq : (bwdSubgraph m (fwdTiling m M hM)).Adj = M.Adj :=
    funext fun v => funext fun w => propext (hAdj v w)
  exact Subgraph.ext hverts hAdjEq

/--
The number of domino tilings, as perfect matchings, of `W_4 □ P_{n-1}`
equals `Nat.fib n * pellNumber n` for `n ≥ 2`, with the Pell factor stated via
the canonical `MetaMathlibExt.pellNumber` sequence.

This is the `pellNumber` form of `boxProd_tiling_card_eq_fib_mul_pell`, which
keeps the inline `Nat.rec` spelling of the Pell factor for the `Wanted` entry.
-/
theorem boxProd_tiling_card_eq_fib_mul_pellNumber :
    ∀ (n : ℕ) (_hn : 2 ≤ n),
      Nat.card { M : (((SimpleGraph.completeGraph (Fin 4)).deleteEdges
        {Sym2.mk (0 : Fin 4) (1 : Fin 4)} □
        SimpleGraph.pathGraph (n - 1)).Subgraph) // M.IsPerfectMatching } =
        Nat.fib n * pellNumber n := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hclosed : Nat.fib (m + 1) * pellNumber (m + 1) = dval m := by
    unfold dval
    rw [pell_eq_pellNumber]
  rw [hclosed]
  have hsub : m + 1 - 1 = m := rfl
  rw [hsub]
  have hAval : Aval m = dval m := Aval_eq_dval m
  rw [←hAval]
  unfold Aval Ncount
  change Nat.card { M : (W4 □ pathGraph m).Subgraph // M.IsPerfectMatching } =
    Fintype.card (Tiling m ∅)
  have e : { M : (W4 □ pathGraph m).Subgraph // M.IsPerfectMatching } ≃
      Tiling m ∅ :=
    { toFun := fun M => fwdTiling m M.val M.property
      invFun := fun t => ⟨bwdSubgraph m t, bwdSubgraph_perfect m t⟩
      left_inv := fun M => by
        have h : bwdSubgraph m (fwdTiling m M.val M.property) = M.val :=
          bwd_fwd_eq m M.val M.property
        exact Subtype.ext h
      right_inv := fun t => fwd_bwd_eq m t }
  calc Nat.card { M : (W4 □ pathGraph m).Subgraph // M.IsPerfectMatching }
      = Nat.card (Tiling m ∅) := Nat.card_congr e
    _ = Fintype.card (Tiling m ∅) := Nat.card_eq_fintype_card

end MetaMathlibExt
end
