import Mathlib
import sympy.Basic


namespace MathlibExt.Combinatorics.SimpleGraph.OreWanted

/--
[hamiltonian_of_cyclic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Ore.lean)
-/
@[path]
# Ore's lemma
Hamiltonian cycle from degree sum of nonadjacent vertices.
-/
/-- A graph on at least three vertices is Hamiltonian if some cyclic enumeration `e` of its
vertices has every consecutive pair `e i`, `e (i + 1)` adjacent. -/
private theorem hamiltonian_of_cyclic {W : Type*} [Fintype W] [DecidableEq W]
  [NeZero (Fintype.card W)]
  (G : SimpleGraph W)
  (e : Fin (Fintype.card W) → W)
  (hN : 3 ≤ Fintype.card W)
  (hinj : Function.Injective e) (hsurj : Function.Surjective e)
  (hadj : ∀ i : Fin (Fintype.card W), G.Adj (e i) (e (i + 1))) :
  G.IsHamiltonian := by
  classical
  have hNpos : 0 < Fintype.card W := by omega
  set y : ℕ → W := fun t => e ⟨t % Fintype.card W, Nat.mod_lt _ hNpos⟩ with hy
  have hval : ∀ i : Fin (Fintype.card W),
    ((i + 1 : Fin (Fintype.card W))).val = (i.val + 1) % Fintype.card W := by
    intro i
    simp [Fin.val_add]
  have hmod_add : ∀ t : ℕ,
    (t % Fintype.card W + 1) % Fintype.card W = (t + 1) % Fintype.card W :=
    fun t => Nat.mod_add_mod t (Fintype.card W) 1
  have yadj : ∀ t : ℕ, G.Adj (y t) (y (t + 1)) := by
    intro t
    have h := hadj ⟨t % Fintype.card W, Nat.mod_lt _ hNpos⟩
    have heq : ((⟨t % Fintype.card W, Nat.mod_lt _ hNpos⟩ + 1 :
      Fin (Fintype.card W))) = ⟨(t + 1) % Fintype.card W, Nat.mod_lt _ hNpos⟩ := by
      apply Fin.ext
      rw [hval]
      exact hmod_add t
    rwa [heq] at h
  have hwalk : ∀ m : ℕ, ∃ p : G.Walk (e 0) (y m),
    p.support = List.map y (List.range (m + 1)) ∧
    p.edges = List.map (fun t => s(y t, y (t + 1))) (List.range m) ∧
    p.length = m := by
    intro m
    induction m with
    | zero =>
      refine ⟨SimpleGraph.Walk.nil, ?_, rfl, rfl⟩
      change [e 0] = List.map y (List.range (0 + 1))
      rw [show (0 : ℕ) + 1 = 1 from rfl, List.range_one, List.map_singleton]
      congr 1
    | succ m ih =>
      obtain ⟨p, hsupp, hedges, hlen⟩ := ih
      refine ⟨p.concat (yadj m), ?_, ?_, ?_⟩
      · rw [SimpleGraph.Walk.support_concat, hsupp, List.range_succ (n := m + 1),
        List.map_append, List.map_singleton]
      · rw [SimpleGraph.Walk.edges_concat, hedges, List.range_succ (n := m),
        List.map_append, List.concat_eq_append, List.map_singleton]
      · rw [SimpleGraph.Walk.length_concat, hlen]
  obtain ⟨p, hsupp, hedges, hlen⟩ := hwalk (Fintype.card W)
  have hyN : y (Fintype.card W) = e 0 := by
    change e ⟨Fintype.card W % Fintype.card W, _⟩ = e 0
    simp only [Nat.mod_self]
    simp
  obtain ⟨q, hqsupp, hqedges, hqlen⟩ :
    ∃ q : G.Walk (e 0) (e 0),
      q.support = List.map y (List.range (Fintype.card W + 1)) ∧
      q.edges = List.map (fun t => s(y t, y (t + 1))) (List.range (Fintype.card W)) ∧
      q.length = Fintype.card W :=
    ⟨p.copy rfl hyN,
      by rw [SimpleGraph.Walk.support_copy, hsupp],
      by rw [SimpleGraph.Walk.edges_copy, hedges],
      by rw [SimpleGraph.Walk.length_copy, hlen]⟩
  have hmod_succ_inj : ∀ a b : ℕ, a < Fintype.card W → b < Fintype.card W →
    (a + 1) % Fintype.card W = (b + 1) % Fintype.card W → a = b := by
    intro a b ha hb h
    have ha1 : a + 1 < Fintype.card W ∨ a + 1 = Fintype.card W := by omega
    have hb1 : b + 1 < Fintype.card W ∨ b + 1 = Fintype.card W := by omega
    obtain ha1 | ha1 <;> rcases hb1 with hb1 | hb1 := ha1
    · rw [Nat.mod_eq_of_lt ha1, Nat.mod_eq_of_lt hb1] at h; omega
    · rw [Nat.mod_eq_of_lt ha1, hb1, Nat.mod_self] at h; omega
    · rw [ha1, Nat.mod_self, Nat.mod_eq_of_lt hb1] at h; omega
    · omega
  have hmod_cross : ∀ a b : ℕ, a < Fintype.card W → b < Fintype.card W →
    a % Fintype.card W = (b + 1) % Fintype.card W →
    (a + 1) % Fintype.card W = b % Fintype.card W → False := by
    intro a b ha hb h1 h2
    rw [Nat.mod_eq_of_lt ha] at h1; rw [Nat.mod_eq_of_lt hb] at h2
    have hb1 : b + 1 < Fintype.card W ∨ b + 1 = Fintype.card W := by omega
    obtain hb1 | hb1 := hb1
    · rw [Nat.mod_eq_of_lt hb1] at h1
      have h2' : (b + 2) % Fintype.card W = b := by
        have hba : a + 1 = b + 2 := by omega
        rw [hba] at h2; exact h2
      have hb2 : b + 2 < Fintype.card W ∨ b + 2 = Fintype.card W ∨
        b + 2 = Fintype.card W + 1 := by omega
      obtain hb2 | hb2 | hb2 := hb2
      · rw [Nat.mod_eq_of_lt hb2] at h2'; omega
      · rw [show b + 2 = Fintype.card W from hb2, Nat.mod_self] at h2'; omega
      · rw [show b + 2 = Fintype.card W + 1 from hb2, Nat.add_mod_left,
        Nat.mod_eq_of_lt (by omega : 1 < Fintype.card W)] at h2'; omega
    · rw [hb1, Nat.mod_self] at h1
      rw [show a + 1 = 1 from by omega,
        Nat.mod_eq_of_lt (by omega : 1 < Fintype.card W)] at h2
      omega
  have hy_inj : ∀ s t : ℕ, y s = y t →
    s % Fintype.card W = t % Fintype.card W := by
    intro s t h
    have h2 := hinj h
    exact Fin.ext_iff.mp h2
  have htail_eq : q.support.tail =
    List.map (fun t => y (t + 1)) (List.range (Fintype.card W)) := by
    rw [hqsupp, List.range_succ_eq_map, List.map_cons, List.tail_cons, List.map_map]
    have hfun : (y ∘ Nat.succ) = (fun t => y (t + 1)) := funext fun t => rfl
    rw [hfun]
  have htail_nodup : q.support.tail.Nodup := by
    rw [htail_eq, List.nodup_iff_injective_getElem]
    intro a b hab
    have hlen_map : (List.map (fun t => y (t + 1))
      (List.range (Fintype.card W))).length = Fintype.card W := by simp
    have haN : (a : ℕ) < Fintype.card W := by have h := a.isLt; omega
    have hbN : (b : ℕ) < Fintype.card W := by have h := b.isLt; omega
    simp only [List.getElem_map, List.getElem_range] at hab
    have h2 := hy_inj _ _ hab
    have h3 := hmod_succ_inj _ _ haN hbN h2
    exact Fin.ext h3
  have hedges_nodup : q.edges.Nodup := by
    rw [hqedges, List.nodup_iff_injective_getElem]
    intro a b hab
    have hlen_map : (List.map (fun t => s(y t, y (t + 1)))
      (List.range (Fintype.card W))).length = Fintype.card W := by simp
    have haN : (a : ℕ) < Fintype.card W := by have h := a.isLt; omega
    have hbN : (b : ℕ) < Fintype.card W := by have h := b.isLt; omega
    simp only [List.getElem_map, List.getElem_range] at hab
    rw [Sym2.eq_iff] at hab
    obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := hab
    · have e1 := hy_inj _ _ h1
      rw [Nat.mod_eq_of_lt haN, Nat.mod_eq_of_lt hbN] at e1
      exact Fin.ext e1
    · have e1 := hy_inj _ _ h1
      have e2 := hy_inj _ _ h2
      exact False.elim (hmod_cross _ _ haN hbN e1 e2)
  have hNnil : ¬ q.Nil := by
    intro h
    have h0 : q.length = 0 := SimpleGraph.Walk.length_eq_zero_iff.mpr h
    omega
  have htail_supp : (q.tail).support = q.support.tail :=
    SimpleGraph.Walk.support_tail_of_not_nil q hNnil
  have htail_path : q.tail.IsPath := by
    apply SimpleGraph.Walk.IsPath.mk'
    rw [htail_supp]; exact htail_nodup
  have htail_mem : ∀ w : W, w ∈ (q.tail).support := by
    intro w
    obtain ⟨i, rfl⟩ := hsurj w
    rw [htail_supp, htail_eq]
    by_cases hi0 : i.val = 0
    · have hi : i = 0 := Fin.ext hi0
      subst hi
      have hmem : Fintype.card W - 1 ∈ List.range (Fintype.card W) :=
        List.mem_range.mpr (by omega)
      have hmap : y (Fintype.card W - 1 + 1) ∈
        List.map (fun t => y (t + 1)) (List.range (Fintype.card W)) :=
        List.mem_map_of_mem hmem
      have hyeq : y (Fintype.card W - 1 + 1) = e (0 : Fin (Fintype.card W)) := by
        have h1 : Fintype.card W - 1 + 1 = Fintype.card W := by omega
        rw [h1, hyN]
      rwa [hyeq] at hmap
    · have hmem : i.val - 1 ∈ List.range (Fintype.card W) :=
      List.mem_range.mpr (by omega)
      have hmap : y (i.val - 1 + 1) ∈
        List.map (fun t => y (t + 1)) (List.range (Fintype.card W)) :=
        List.mem_map_of_mem hmem
      have hyeq : y (i.val - 1 + 1) = e i := by
        have h1 : i.val - 1 + 1 = i.val := by omega
        rw [h1]
        obtain ⟨v, hv⟩ := i
        simp only [hy, Nat.mod_eq_of_lt hv]
      rwa [hyeq] at hmap
  have hham_tail : q.tail.IsHamiltonian :=
    htail_path.isHamiltonian_of_mem htail_mem
  have htrail : q.IsTrail := ⟨hedges_nodup⟩
  have hne : q ≠ SimpleGraph.Walk.nil := by
    intro h
    subst h
    rw [SimpleGraph.Walk.length_nil] at hqlen
    omega
  have hcyc : q.IsCycle := ⟨⟨htrail, hne⟩, htail_nodup⟩
  have hhamc : q.IsHamiltonianCycle := ⟨hcyc, hham_tail⟩
  intro _
  exact ⟨e 0, q, hhamc⟩

end MathlibExt.Combinatorics.SimpleGraph.OreWanted

namespace MathlibExt.Combinatorics.SimpleGraph.OreWanted

/--
[hamiltonian_of_complete](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Ore.lean)
-/
@[path]
private lemma hamiltonian_of_complete {W : Type*} [Fintype W] [DecidableEq W]
  (G : SimpleGraph W)
  (hN : 3 ≤ Fintype.card W)
  (hcomp : ∀ u v : W, u ≠ v → G.Adj u v) :
  G.IsHamiltonian := by
  classical
  have : NeZero (Fintype.card W) := ⟨by omega⟩
  have hval : ∀ i : Fin (Fintype.card W),
    ((i + 1 : Fin (Fintype.card W))).val = (i.val + 1) % Fintype.card W :=
    fun i => by simp [Fin.val_add]
  have hne_i : ∀ i : Fin (Fintype.card W), i ≠ i + 1 := by
    intro i hcon
    have hi := i.isLt
    have hv := congrArg Fin.val hcon
    rw [hval] at hv
    by_cases h : i.val + 1 < Fintype.card W
    · rw [Nat.mod_eq_of_lt h] at hv; omega
    · have hN1 : i.val + 1 = Fintype.card W := by omega
      rw [hN1, Nat.mod_self] at hv; omega
  exact hamiltonian_of_cyclic G (fun i => (Fintype.equivFin W).symm i) hN
    (Fintype.equivFin W).symm.injective (Fintype.equivFin W).symm.surjective
    (fun i => hcomp _ _ (fun h => hne_i i ((Fintype.equivFin W).symm.injective h)))

end MathlibExt.Combinatorics.SimpleGraph.OreWanted

namespace MathlibExt.Combinatorics.SimpleGraph.OreWanted

/--
[transfer_hampath](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Ore.lean)
-/
@[path]
private lemma transfer_hampath {W : Type*} [DecidableEq W]
  (G G' : SimpleGraph W)
  {x y : W} (Q : G'.Walk x y) (hpath : Q.IsPath) (hham : Q.IsHamiltonian)
  (hprem : ∀ e ∈ Q.edges, e ∈ G.edgeSet) :
  ∃ P : G.Walk x y, P.IsPath ∧ P.IsHamiltonian := by
  classical
  refine ⟨Q.transfer G hprem, ?_, ?_⟩
  · exact (SimpleGraph.Walk.isPath_transfer hprem).mpr hpath
  · intro w
    have hsupp := SimpleGraph.Walk.support_transfer Q hprem
    rw [hsupp]
    exact hham w

end MathlibExt.Combinatorics.SimpleGraph.OreWanted

namespace MathlibExt.Combinatorics.SimpleGraph.OreWanted

/--
[ore_splice](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Ore.lean)
-/
@[path]
private lemma ore_splice {W : Type*} [Fintype W] [DecidableEq W]
  (G : SimpleGraph W) [DecidableRel G.Adj]
  {a b : W} (p : G.Walk a b) (hp_path : p.IsPath) (hp_ham : p.IsHamiltonian)
  (hN : 3 ≤ Fintype.card W)
  (_hne : a ≠ b) (_hnadj : ¬G.Adj a b)
  (hdeg : Fintype.card W ≤ G.degree a + G.degree b) :
  G.IsHamiltonian := by
  have : NeZero (Fintype.card W) := ⟨by omega⟩
  have hlen : p.length = Fintype.card W - 1 :=
    (SimpleGraph.Walk.isHamiltonian_iff_isPath_and_length_eq.mp hp_ham).2
  have hsupplen : p.support.length = Fintype.card W := hp_ham.length_support
  have gv_inj : ∀ x y : ℕ, x < Fintype.card W → y < Fintype.card W →
    p.getVert x = p.getVert y → x = y := by
    intro x y hx hy h
    exact hp_path.getVert_injOn (show x ≤ p.length from by omega)
      (show y ≤ p.length from by omega) h
  have gv0 : p.getVert 0 = a := p.getVert_zero
  have gvL : p.getVert (Fintype.card W - 1) = b := by
    rwa [show Fintype.card W - 1 = p.length from by omega]
  set S' : Finset ℕ := (Finset.range (Fintype.card W - 1)).filter
    (fun j => G.Adj a (p.getVert (j + 1))) with hS'def
  set T : Finset ℕ := (Finset.range (Fintype.card W - 1)).filter
    (fun j => G.Adj (p.getVert j) b) with hT'def
  have hidx : ∀ j : ℕ, j < Fintype.card W → p.support.idxOf (p.getVert j) = j := by
    intro j hj
    have hmem : p.getVert j ∈ p.support := p.getVert_mem_support j
    have hm : p.support.idxOf (p.getVert j) < Fintype.card W := by
      have h3 := List.idxOf_lt_length_of_mem hmem
      rwa [hsupplen] at h3
    have heq := p.getVert_support_idxOf hmem
    exact gv_inj _ _ hm hj heq
  have hidx_ne : ∀ w : W, G.Adj a w → p.support.idxOf w ≠ 0 := by
    intro w hwa h0
    have hmem : w ∈ p.support := hp_ham.mem_support w
    have heq := p.getVert_support_idxOf hmem
    rw [h0, gv0] at heq
    exact hwa.ne heq
  have hidx_ne' : ∀ w : W, G.Adj w b → p.support.idxOf w ≠ Fintype.card W - 1 := by
    intro w hwb h0
    have hmem : w ∈ p.support := hp_ham.mem_support w
    have heq := p.getVert_support_idxOf hmem
    rw [h0, gvL] at heq
    exact hwb.ne heq.symm
  have hcardS : S'.card = G.degree a := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree, eq_comm]
    apply Finset.card_bij (fun w _ => p.support.idxOf w - 1)
    · intro w hw
      have hwa : G.Adj a w := (SimpleGraph.mem_neighborFinset G a w).mp hw
      have hmem : w ∈ p.support := hp_ham.mem_support w
      have hjN : p.support.idxOf w < Fintype.card W := by
        have h3 := List.idxOf_lt_length_of_mem hmem
        rwa [hsupplen] at h3
      have hj0 := hidx_ne w hwa
      have hmemS : p.support.idxOf w - 1 ∈ S' := by
        rw [hS'def, Finset.mem_filter, Finset.mem_range]
        refine ⟨by omega, ?_⟩
        have h1 : p.support.idxOf w - 1 + 1 = p.support.idxOf w := by omega
        rw [h1]
        have heq := p.getVert_support_idxOf hmem
        rwa [heq]
      exact hmemS
    · intro w1 hw1 w2 hw2 h12
      have hwa1 := (SimpleGraph.mem_neighborFinset G a w1).mp hw1
      have hwa2 := (SimpleGraph.mem_neighborFinset G a w2).mp hw2
      have e12 : p.support.idxOf w1 = p.support.idxOf w2 := by
        have n1 := hidx_ne w1 hwa1
        have n2 := hidx_ne w2 hwa2
        omega
      have m1 := hp_ham.mem_support w1
      have m2 := hp_ham.mem_support w2
      have g1 := p.getVert_support_idxOf m1
      have g2 := p.getVert_support_idxOf m2
      rw [e12] at g1
      exact g1.symm.trans g2
    · intro k hk
      rw [hS'def, Finset.mem_filter, Finset.mem_range] at hk
      obtain ⟨hkR, hkA⟩ := hk
      have hk1 : k + 1 < Fintype.card W := by omega
      refine ⟨p.getVert (k + 1),
        (SimpleGraph.mem_neighborFinset G a _).mpr hkA, ?_⟩
      have hkk := hidx (k + 1) hk1
      change p.support.idxOf (p.getVert (k + 1)) - 1 = k
      omega
  have hcardT : T.card = G.degree b := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree, eq_comm]
    apply Finset.card_bij (fun w _ => p.support.idxOf w)
    · intro w hw
      have hwb : G.Adj w b :=
        ((SimpleGraph.mem_neighborFinset G b w).mp hw).symm
      have hmem : w ∈ p.support := hp_ham.mem_support w
      have hjN : p.support.idxOf w < Fintype.card W := by
        have h3 := List.idxOf_lt_length_of_mem hmem
        rwa [hsupplen] at h3
      have hjN1 := hidx_ne' w hwb
      have hmemT : p.support.idxOf w ∈ T := by
        rw [hT'def, Finset.mem_filter, Finset.mem_range]
        refine ⟨by omega, ?_⟩
        have heq := p.getVert_support_idxOf hmem
        rwa [heq]
      exact hmemT
    · intro w1 hw1 w2 hw2 h12
      have m1 := hp_ham.mem_support w1
      have m2 := hp_ham.mem_support w2
      have g1 := p.getVert_support_idxOf m1
      have g2 := p.getVert_support_idxOf m2
      rw [h12] at g1
      exact g1.symm.trans g2
    · intro k hk
      rw [hT'def, Finset.mem_filter, Finset.mem_range] at hk
      obtain ⟨hkR, hkA⟩ := hk
      have hk1 : k < Fintype.card W := by omega
      refine ⟨p.getVert k, (SimpleGraph.mem_neighborFinset G b _).mpr hkA.symm, ?_⟩
      have hkk := hidx k hk1
      change p.support.idxOf (p.getVert k) = k
      omega
  have hsub : S' ∪ T ⊆ Finset.range (Fintype.card W - 1) :=
    Finset.union_subset
      (by simp [hS'def])
      (by simp [hT'def])
  have hle : (S' ∪ T).card ≤ Fintype.card W - 1 :=
    le_trans (Finset.card_le_card hsub) (by simp)
  have hunion := Finset.card_union_add_card_inter S' T
  rw [hcardS, hcardT] at hunion
  have hinter : 0 < (S' ∩ T).card := by omega
  obtain ⟨k, hk⟩ := Finset.card_pos.mp hinter
  obtain ⟨hkS, hkT⟩ := Finset.mem_inter.mp hk
  rw [hS'def, Finset.mem_filter, Finset.mem_range] at hkS
  rw [hT'def, Finset.mem_filter, Finset.mem_range] at hkT
  obtain ⟨hkR, hkA⟩ := hkS
  obtain ⟨-, hkB⟩ := hkT
  have hkN : k + 1 < Fintype.card W := by omega
  set f : Fin (Fintype.card W) → W := fun i =>
    if i.val ≤ k then p.getVert i.val
    else p.getVert (Fintype.card W - 1 - (i.val - (k + 1))) with hfdef
  have hf_val : ∀ i : Fin (Fintype.card W), f i =
    (if i.val ≤ k then p.getVert i.val
    else p.getVert (Fintype.card W - 1 - (i.val - (k + 1)))) := fun i => rfl
  have hinj_f : Function.Injective f := by
    intro i j hij
    rw [hf_val, hf_val] at hij
    by_cases hi : i.val ≤ k <;> by_cases hj : j.val ≤ k
    · simp only [hi, hj, ite_true] at hij
      have hpos := gv_inj _ _ (by omega) (by omega) hij
      exact Fin.ext hpos
    · simp only [hi, hj, ite_true, ite_false] at hij
      have hpos := gv_inj _ _ (by omega) (by omega) hij
      have hcon : False := by omega
      exact hcon.elim
    · simp only [hi, hj, ite_true, ite_false] at hij
      have hpos := gv_inj _ _ (by omega) (by omega) hij
      have hcon : False := by omega
      exact hcon.elim
    · simp only [hi, hj, ite_false] at hij
      have hpos := gv_inj _ _ (by omega) (by omega) hij
      have heq : i.val = j.val := by omega
      exact Fin.ext heq
  have hsurj_f : Function.Surjective f := by
    intro w
    obtain ⟨t, ht_eq, ht_le⟩ :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mp (hp_ham.mem_support w)
    have htN : t < Fintype.card W := by omega
    by_cases ht : t ≤ k
    · refine ⟨⟨t, htN⟩, ?_⟩
      rwa [hf_val, ite_eq_left ht]
    · refine ⟨⟨k + 1 + (Fintype.card W - 1 - t), by omega⟩, ?_⟩
      rw [hf_val]
      have hnk : ¬ (k + 1 + (Fintype.card W - 1 - t)) ≤ k := by omega
      rw [ite_eq_right hnk]
      have hidx_eq : Fintype.card W - 1 - ((k + 1 + (Fintype.card W - 1 - t)) - (k + 1))
        = t := by omega
      rwa [hidx_eq]
  have hsucc : ∀ i : Fin (Fintype.card W),
    ((i + 1 : Fin (Fintype.card W))).val = (i.val + 1) % Fintype.card W :=
    fun i => by simp [Fin.val_add]
  have hadj_f : ∀ i : Fin (Fintype.card W), G.Adj (f i) (f (i + 1)) := by
    intro i
    rw [hf_val, hf_val, hsucc i]
    by_cases hi : i.val < k
    · have h1 : i.val ≤ k := by omega
      have hmod : (i.val + 1) % Fintype.card W = i.val + 1 :=
        Nat.mod_eq_of_lt (by omega)
      have h2 : (i.val + 1) % Fintype.card W ≤ k := by rw [hmod]; omega
      rw [ite_eq_left h1, ite_eq_left h2, hmod]
      exact p.adj_getVert_succ (by omega)
    · by_cases hik : i.val = k
      · rw [hik]
        have hmod : (k + 1) % Fintype.card W = k + 1 := Nat.mod_eq_of_lt hkN
        have h2 : ¬ (k + 1) % Fintype.card W ≤ k := by rw [hmod]; omega
        rw [ite_eq_left (le_refl k), ite_eq_right h2, hmod]
        have hidx_eq : Fintype.card W - 1 - ((k + 1) - (k + 1))
          = Fintype.card W - 1 := by omega
        rwa [hidx_eq, gvL]
      · by_cases hiN : i.val = Fintype.card W - 1
        · have h1 : ¬ i.val ≤ k := by omega
          have hmod : (i.val + 1) % Fintype.card W = 0 := by
            rw [hiN, show Fintype.card W - 1 + 1 = Fintype.card W from by omega,
              Nat.mod_self]
          have h2 : (i.val + 1) % Fintype.card W ≤ k := by rw [hmod]; omega
          rw [ite_eq_right h1, ite_eq_left h2, hmod, hiN]
          have hmidx : Fintype.card W - 1 - ((Fintype.card W - 1) - (k + 1))
            = k + 1 := by omega
          rwa [hmidx, gv0]
        · have h1 : ¬ i.val ≤ k := by omega
          have hmod : (i.val + 1) % Fintype.card W = i.val + 1 :=
            Nat.mod_eq_of_lt (by omega)
          have h2 : ¬ (i.val + 1) % Fintype.card W ≤ k := by rw [hmod]; omega
          rw [ite_eq_right h1, ite_eq_right h2, hmod]
          have hm : Fintype.card W - 1 - ((i.val + 1) - (k + 1))
            = (Fintype.card W - 1 - (i.val - (k + 1))) - 1 := by omega
          rw [hm]
          have hstep := (p.adj_getVert_succ
            (show Fintype.card W - 1 - (i.val - (k + 1)) - 1 < p.length from by omega)).symm
          rw [show Fintype.card W - 1 - (i.val - (k + 1)) - 1 + 1
            = Fintype.card W - 1 - (i.val - (k + 1)) from by omega] at hstep
          exact hstep
  exact hamiltonian_of_cyclic G f hN hinj_f hsurj_f hadj_f

end MathlibExt.Combinatorics.SimpleGraph.OreWanted

namespace MathlibExt.Combinatorics.SimpleGraph.OreWanted

/--
[ore_aux](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Ore.lean)
-/
@[path]
private lemma ore_aux {W : Type*} [Fintype W] [DecidableEq W] :
  ∀ (m : ℕ) (G : SimpleGraph W) [DecidableRel G.Adj],
  3 ≤ Fintype.card W →
  (∀ u v : W, u ≠ v → ¬G.Adj u v → Fintype.card W ≤ G.degree u + G.degree v) →
  ((⊤ : SimpleGraph W).edgeFinset.filter (fun e => e ∉ G.edgeSet)).card ≤ m →
  G.IsHamiltonian := by
  intro m
  induction m with
  | zero =>
    intro G _ hcard hdeg hmiss
    have hempty : (⊤ : SimpleGraph W).edgeFinset.filter (fun e => e ∉ G.edgeSet)
      = ∅ := Finset.card_eq_zero.mp (by omega)
    have hcomp : ∀ u v : W, u ≠ v → G.Adj u v := by
      intro u v hne
      have heTop : s(u, v) ∈ (⊤ : SimpleGraph W).edgeFinset :=
        (SimpleGraph.mem_edgeFinset).mpr
          ((SimpleGraph.mem_edgeSet _).mpr ((SimpleGraph.top_adj u v).mpr hne))
      have hnotin : s(u, v) ∉ (⊤ : SimpleGraph W).edgeFinset.filter
        (fun e => e ∉ G.edgeSet) := by
        rw [hempty]; exact Finset.notMem_empty _
      rw [Finset.mem_filter] at hnotin
      push Not at hnotin
      have hG : s(u, v) ∈ G.edgeSet := hnotin heTop
      exact (SimpleGraph.mem_edgeSet G).mp hG
    exact hamiltonian_of_complete G hcard hcomp
  | succ m ih =>
    intro G _ hcard hdeg hmiss
    by_cases hcomp : ∀ u v : W, u ≠ v → G.Adj u v
    · exact hamiltonian_of_complete G hcard hcomp
    · push Not at hcomp
      obtain ⟨u, v, hne, hnadj⟩ := hcomp
      have hmem_top : s(u, v) ∈ (⊤ : SimpleGraph W).edgeFinset :=
        (SimpleGraph.mem_edgeFinset).mpr
          ((SimpleGraph.mem_edgeSet _).mpr ((SimpleGraph.top_adj u v).mpr hne))
      have hmem_notG : s(u, v) ∉ G.edgeSet := by
        intro hc
        exact hnadj ((SimpleGraph.mem_edgeSet G).mp hc)
      have hmem_F : s(u, v) ∈ (SimpleGraph.fromEdgeSet {s(u, v)}).edgeSet :=
        (SimpleGraph.mem_edgeSet _).mpr
          ((SimpleGraph.fromEdgeSet_adj _).mpr ⟨(Set.mem_singleton_iff).mpr rfl, hne⟩)
      have hmem_G' : s(u, v) ∈ (G ⊔ SimpleGraph.fromEdgeSet {s(u, v)}).edgeSet := by
        rw [SimpleGraph.edgeSet_sup]
        exact Or.inr hmem_F
      have hsub : (⊤ : SimpleGraph W).edgeFinset.filter
        (fun e => e ∉ (G ⊔ SimpleGraph.fromEdgeSet {s(u, v)}).edgeSet) ⊆
        (⊤ : SimpleGraph W).edgeFinset.filter (fun e => e ∉ G.edgeSet) := by
        intro e he
        rw [Finset.mem_filter] at he ⊢
        obtain ⟨heT, heG'⟩ := he
        refine ⟨heT, ?_⟩
        intro heG
        have hle : G ≤ G ⊔ SimpleGraph.fromEdgeSet {s(u, v)} := le_sup_left
        exact heG' ((SimpleGraph.edgeSet_mono hle) heG)
      have h1mem : s(u, v) ∈ (⊤ : SimpleGraph W).edgeFinset.filter
        (fun e => e ∉ G.edgeSet) :=
        Finset.mem_filter.mpr ⟨hmem_top, hmem_notG⟩
      have h1not : s(u, v) ∉ (⊤ : SimpleGraph W).edgeFinset.filter
        (fun e => e ∉ (G ⊔ SimpleGraph.fromEdgeSet {s(u, v)}).edgeSet) := by
        intro hcon
        have h2 := (Finset.mem_filter.mp hcon).2
        exact h2 hmem_G'
      have hne_set : (⊤ : SimpleGraph W).edgeFinset.filter
        (fun e => e ∉ (G ⊔ SimpleGraph.fromEdgeSet {s(u, v)}).edgeSet) ≠
        (⊤ : SimpleGraph W).edgeFinset.filter (fun e => e ∉ G.edgeSet) := by
        intro hcon
        exact h1not (hcon ▸ h1mem)
      have hss : (⊤ : SimpleGraph W).edgeFinset.filter
        (fun e => e ∉ (G ⊔ SimpleGraph.fromEdgeSet {s(u, v)}).edgeSet) ⊂
        (⊤ : SimpleGraph W).edgeFinset.filter (fun e => e ∉ G.edgeSet) :=
        Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne_set⟩
      have hlt := Finset.card_lt_card hss
      have hmiss' : ((⊤ : SimpleGraph W).edgeFinset.filter
        (fun e => e ∉ (G ⊔ SimpleGraph.fromEdgeSet {s(u, v)}).edgeSet)).card
        ≤ m := by omega
      have hdeg' : ∀ u1 v1 : W, u1 ≠ v1 →
        ¬(G ⊔ SimpleGraph.fromEdgeSet {s(u, v)}).Adj u1 v1 →
        Fintype.card W ≤ (G ⊔ SimpleGraph.fromEdgeSet {s(u, v)}).degree u1 +
          (G ⊔ SimpleGraph.fromEdgeSet {s(u, v)}).degree v1 := by
        intro u1 v1 hne1 hnadj1
        have hle : G ≤ G ⊔ SimpleGraph.fromEdgeSet {s(u, v)} := le_sup_left
        have hnG : ¬G.Adj u1 v1 := fun h =>
          hnadj1 ((SimpleGraph.mem_edgeSet _).mp
            ((SimpleGraph.edgeSet_mono hle) ((SimpleGraph.mem_edgeSet G).mpr h)))
        have hdo := hdeg u1 v1 hne1 hnG
        have hle_deg := Nat.add_le_add
          (SimpleGraph.degree_le_of_le (v := u1) hle)
          (SimpleGraph.degree_le_of_le (v := v1) hle)
        omega
      have hG'Ham := ih (G ⊔ SimpleGraph.fromEdgeSet {s(u, v)}) hcard hdeg' hmiss'
      have hnt : Nontrivial W :=
        Fintype.one_lt_card_iff_nontrivial.mp (by omega)
      obtain ⟨q, hq⟩ := hG'Ham.exists_isHamiltonianCycle u
      have hqlen : q.length = Fintype.card W := hq.length_eq
      have hlen_e : q.edges.length = Fintype.card W := by
        have h1 := SimpleGraph.Walk.length_edges q
        omega
      have hqNnil : ¬ q.Nil := by
        intro h
        have h0 : q.length = 0 := SimpleGraph.Walk.length_eq_zero_iff.mpr h
        omega
      have hq_nodup : q.edges.Nodup := hq.isCycle.1.1.edges_nodup
      have hq_tail_nodup : q.support.tail.Nodup := hq.isCycle.support_nodup
      have hu_uniq : ∀ t : ℕ, t ≤ Fintype.card W → q.getVert t = u →
        t = 0 ∨ t = Fintype.card W := by
        intro t ht htu
        by_cases h : t ≤ Fintype.card W - 1
        · left
          have h0 : q.getVert 0 = u := q.getVert_zero
          exact hq.isCycle.getVert_injOn'
            (show t ≤ q.length - 1 from by omega)
            (show (0 : ℕ) ≤ q.length - 1 from by omega)
            (htu.trans h0.symm)
        · right
          omega
      have hFmem : ∀ e : Sym2 W, e ∈ (SimpleGraph.fromEdgeSet {s(u, v)}).edgeSet →
        e = s(u, v) := by
        intro e he
        rw [SimpleGraph.edgeSet_fromEdgeSet] at he
        exact (Set.mem_singleton_iff).mp ((Set.mem_sdiff _).mp he).1
      have hclass : ∀ e ∈ q.edges, e ∈ G.edgeSet ∨ e = s(u, v) := by
        intro e he
        have he' : e ∈ (G ⊔ SimpleGraph.fromEdgeSet {s(u, v)}).edgeSet :=
          q.edges_subset_edgeSet he
        rw [SimpleGraph.edgeSet_sup] at he'
        obtain hG | hF := he'
        · exact Or.inl hG
        · exact Or.inr (hFmem e hF)
      have htail_supp : (q.tail).support = q.support.tail :=
        SimpleGraph.Walk.support_tail_of_not_nil q hqNnil
      have htail_path : (q.tail).IsPath := by
        apply SimpleGraph.Walk.IsPath.mk'
        rw [htail_supp]; exact hq_tail_nodup
      have htail_mem : ∀ w : W, w ∈ (q.tail).support := by
        intro w
        have hcard2 : ((q.tail).support.toFinset).card = Fintype.card W := by
          rw [htail_supp, List.toFinset_card_of_nodup hq_tail_nodup]
          have hL : q.support.length = Fintype.card W + 1 := by
            have h1 := SimpleGraph.Walk.length_support q
            omega
          have h2 : q.support.tail.length = Fintype.card W := by
            rw [List.length_tail]; omega
          exact h2
        have huniv : (q.tail).support.toFinset = Finset.univ :=
          Finset.eq_univ_of_card _ hcard2
        have hm : w ∈ (q.tail).support.toFinset := by
          rw [huniv]; exact Finset.mem_univ w
        exact List.mem_toFinset.mp hm
      have htail_ham : (q.tail).IsHamiltonian :=
        htail_path.isHamiltonian_of_mem htail_mem
      by_cases huse : s(u, v) ∈ q.edges
      · obtain ⟨j, hjlt, hj_eq⟩ := List.mem_iff_getElem.mp huse
        have hjN : j < Fintype.card W := by omega
        have hstep : q.edges[j]'hjlt = s(q.getVert j, q.getVert (j + 1)) :=
          q.getElem_edges hjlt
        have hstep2 : s(q.getVert j, q.getVert (j + 1)) = s(u, v) := by
          rw [← hstep]; exact hj_eq
        rw [Sym2.eq_iff] at hstep2
        obtain ⟨hg1, hg2⟩ | ⟨hg1, hg2⟩ := hstep2
        · have hj0 : j = 0 := by
          have hju := hu_uniq j (by omega) hg1
          omega
          have hgv1 : q.getVert 1 = v := by
            have h2 := hg2
            rwa [hj0] at h2
          have hsnd : q.snd = v := by
            rw [q.snd_eq_support_getElem_one hqNnil, q.support_getElem_eq_getVert _, hgv1]
          have hpremA : ∀ e ∈ (q.tail).edges, e ∈ G.edgeSet := by
            intro e he
            rw [SimpleGraph.Walk.edges_tail] at he
            have heq : e ∈ q.edges := List.mem_of_mem_tail he
            obtain hG | hFs := hclass e heq
            · exact hG
            · have hhead : q.edges[0]'(by omega) = s(u, v) := by
              have h0 := q.getElem_edges
                (show (0 : ℕ) < q.edges.length from by omega)
              rw [h0, q.getVert_zero, hgv1]
              have heq0 : q.edges[0]'(by omega) = e := by
                rw [hhead]; exact hFs.symm
              obtain ⟨k, hklt, hk_eq⟩ := List.mem_iff_getElem.mp he
              have hlt_len : q.edges.tail.length = q.edges.length - 1 :=
                List.length_tail
              have e1 : q.edges[k + 1]'(by omega) = e := by
                have g := List.getElem_tail hklt
                rw [← g]; exact hk_eq
              have hinj_e := List.nodup_iff_injective_getElem.mp hq_nodup
              have hfin : (⟨k + 1, by omega⟩ : Fin q.edges.length) =
                (⟨0, by omega⟩ : Fin q.edges.length) := by
                apply hinj_e
                change q.edges[k + 1]'(by omega) = q.edges[0]'(by omega)
                rw [e1, heq0]
              have hcon : k + 1 = 0 := congrArg Fin.val hfin
              exact absurd hcon (by omega)
          obtain ⟨P, hPpath, hPham⟩ := transfer_hampath G
            (G ⊔ SimpleGraph.fromEdgeSet {s(u, v)}) (q.tail)
            htail_path htail_ham hpremA
          exact ore_splice G P hPpath hPham hcard
            (by rw [hsnd]; exact Ne.symm hne)
            (by rw [hsnd]; exact fun h => hnadj h.symm)
            (by rw [hsnd]; have hdo := hdeg u v hne hnadj; omega)
        · have hjN1 : j + 1 = Fintype.card W := by
          have hju := hu_uniq (j + 1) (by omega) hg2
          omega
          have hj : j = Fintype.card W - 1 := by omega
          have hgvNm1 : q.getVert (Fintype.card W - 1) = v := by
            rw [← hj]; exact hg1
          have hNu : q.getVert (Fintype.card W) = u := by
            rwa [show Fintype.card W = q.length from hqlen.symm]
          have htake_supp : (q.take (Fintype.card W - 1)).support =
            q.support.take (Fintype.card W) := by
            rw [SimpleGraph.Walk.support_take,
              show Fintype.card W - 1 + 1 = Fintype.card W from by omega]
          have htake_len : (q.take (Fintype.card W - 1)).support.length
            = Fintype.card W := by
            rw [htake_supp, List.length_take]
            have hL : q.support.length = Fintype.card W + 1 := by
              have h1 := SimpleGraph.Walk.length_support q
              omega
            omega
          have htake_nodup : (q.take (Fintype.card W - 1)).support.Nodup := by
            rw [htake_supp, List.nodup_iff_injective_getElem]
            intro a b hab
            have hlen_tk : (q.support.take (Fintype.card W)).length
              = Fintype.card W := by
              rw [List.length_take]
              have hL : q.support.length = Fintype.card W + 1 := by
                have h1 := SimpleGraph.Walk.length_support q
                omega
              omega
            have haN : (a : ℕ) < Fintype.card W := by have h := a.isLt; omega
            have hbN : (b : ℕ) < Fintype.card W := by have h := b.isLt; omega
            simp only [List.getElem_take, q.support_getElem_eq_getVert] at hab
            have heq := hq.isCycle.getVert_injOn'
              (show (a : ℕ) ≤ q.length - 1 from by omega)
              (show (b : ℕ) ≤ q.length - 1 from by omega) hab
            exact Fin.ext heq
          have htake_path : (q.take (Fintype.card W - 1)).IsPath :=
            SimpleGraph.Walk.IsPath.mk' htake_nodup
          have htake_mem : ∀ w : W, w ∈ (q.take (Fintype.card W - 1)).support := by
            intro w
            have hcard2 : ((q.take (Fintype.card W - 1)).support.toFinset).card
              = Fintype.card W := by
              rw [List.toFinset_card_of_nodup htake_nodup, htake_len]
            have huniv : (q.take (Fintype.card W - 1)).support.toFinset
              = Finset.univ := Finset.eq_univ_of_card _ hcard2
            have hm : w ∈ (q.take (Fintype.card W - 1)).support.toFinset := by
              rw [huniv]; exact Finset.mem_univ w
            exact List.mem_toFinset.mp hm
          have htake_ham : (q.take (Fintype.card W - 1)).IsHamiltonian :=
            htake_path.isHamiltonian_of_mem htake_mem
          have hpremB : ∀ e ∈ (q.take (Fintype.card W - 1)).edges, e ∈ G.edgeSet := by
            intro e he
            rw [SimpleGraph.Walk.edges_take] at he
            have heq : e ∈ q.edges := List.mem_of_mem_take he
            obtain hG | hFs := hclass e heq
            · exact hG
            · have hlast : q.edges[Fintype.card W - 1]'(by omega) = s(u, v) := by
              have h0 := q.getElem_edges
                (show Fintype.card W - 1 < q.edges.length from by omega)
              have hplus : Fintype.card W - 1 + 1 = Fintype.card W := by omega
              rwa [h0, hgvNm1, hplus, hNu]
              have heq0 : q.edges[Fintype.card W - 1]'(by omega) = e := by
                rw [hlast]; exact hFs.symm
              obtain ⟨k, hklt, hk_eq⟩ := List.mem_iff_getElem.mp he
              have hlt_len : (q.edges.take (Fintype.card W - 1)).length
                = Fintype.card W - 1 := by
                rw [List.length_take]; omega
              have e1 : q.edges[k]'(by omega) = e := by
                have g := List.getElem_take (xs := q.edges)
                  (j := Fintype.card W - 1) (i := k) (h := hklt)
                exact g.symm.trans hk_eq
              have hinj_e := List.nodup_iff_injective_getElem.mp hq_nodup
              have hfin : (⟨k, by omega⟩ : Fin q.edges.length) =
                (⟨Fintype.card W - 1, by omega⟩ : Fin q.edges.length) := by
                apply hinj_e
                change q.edges[k]'(by omega) = q.edges[Fintype.card W - 1]'(by omega)
                rw [e1, heq0]
              have hcon : k = Fintype.card W - 1 := congrArg Fin.val hfin
              have hklt' : k < Fintype.card W - 1 := by omega
              exact absurd hcon (by omega)
          obtain ⟨P, hPpath, hPham⟩ := transfer_hampath G
            (G ⊔ SimpleGraph.fromEdgeSet {s(u, v)}) (q.take (Fintype.card W - 1))
            htake_path htake_ham hpremB
          exact ore_splice G P hPpath hPham hcard
            (by rw [hgvNm1]; exact hne)
            (by rw [hgvNm1]; exact hnadj)
            (by rw [hgvNm1]; exact hdeg u v hne hnadj)
      · have hprem : ∀ e ∈ q.edges, e ∈ G.edgeSet := by
        intro e he
        obtain hG | hFs := hclass e he
        · exact hG
        · have he' := he
          rw [hFs] at he'
          exact absurd he' huse
        intro _
        refine ⟨u, q.transfer G hprem, ?_⟩
        rw [SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_length_eq]
        refine ⟨?_, ?_⟩
        · exact (SimpleGraph.Walk.isCycle_transfer hprem).mpr hq.isCycle
        · rw [SimpleGraph.Walk.length_transfer q hprem]; exact hqlen

end MathlibExt.Combinatorics.SimpleGraph.OreWanted

namespace MathlibExt.Combinatorics.SimpleGraph.OreWanted

/--
[ore](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Ore.lean)
-/
@[path]
lemma ore
  [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
-- given
  (hcard : 3 ≤ Fintype.card V)
  (hdeg : ∀ u v : V, u ≠ v → ¬G.Adj u v → Fintype.card V ≤ G.degree u + G.degree v) :
-- imply
  G.IsHamiltonian := by
-- proof
  exact ore_aux ((⊤ : SimpleGraph V).edgeFinset.filter (fun e => e ∉ G.edgeSet)).card
    G hcard hdeg le_rfl

end MathlibExt.Combinatorics.SimpleGraph.OreWanted


-- created on 2026-10-20
-- updated on 2026-10-23
