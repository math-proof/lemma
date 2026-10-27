import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Words.CobhamUniformMorphism
open MetaMathlibExt


namespace MetaMathlibExt

/--
[repVal](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/CobhamUniformMorphism.lean)
-/
@[path]
private lemma repVal {k : Nat} (hk : 2 ≤ k) (n : Nat) :
  baseWordValueLSD (repList hk n) = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n = 0
    · subst h; rw [repList.eq_1]; rfl
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h
      have hmem : (m + 1) / k < m + 1 :=
        Nat.div_lt_self (Nat.succ_pos _) (by omega)
      rw [repList.eq_2 hk m]
      change _ + k * baseWordValueLSD (repList hk ((m + 1) / k)) = _
      rw [ih _ hmem]
      exact Nat.mod_add_div _ _

end MetaMathlibExt

namespace MetaMathlibExt

/--
[repCons](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/CobhamUniformMorphism.lean)
-/
@[path]
private lemma repCons {k : Nat} (hk : 2 ≤ k) (n j : Nat) (hj : j < k)
  (hne : k * n + j ≠ 0) :
  repList hk (k * n + j) = ⟨j, hj⟩ :: repList hk n := by
  have hk0 : 0 < k := by omega
  have hmod : (k * n + j) % k = j := by
    rw [add_comm (k * n) j, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
  have hdiv : (k * n + j) / k = n := by
    rw [mul_comm k n, add_comm (n * k) j, Nat.add_mul_div_right j n hk0,
      Nat.div_eq_of_lt hj, zero_add]
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hne
  have e1 : repList hk m.succ =
    ⟨m.succ % k, Nat.mod_lt _ (by omega)⟩ :: repList hk (m.succ / k) :=
    repList.eq_2 hk m
  rw [← hm] at e1
  rw [e1]
  simp only [hmod, hdiv]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[morphComp_val](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/CobhamUniformMorphism.lean)
-/
@[path]
private lemma morphComp_val {q k : Nat} (f : Fin q → List (Fin q)) (a : Fin q)
  (u : Nat → Fin q) (hu0 : u 0 = a)
  (hblock : ∀ n : Nat, ∀ j : Nat, j < k → (f (u n)).getD j a = u (k * n + j))
  (ds : List (Fin k)) :
  morphComp f a ds a = u (baseWordValueLSD ds) := by
  induction ds with
  | nil =>
    have hA : morphComp f a ([] : List (Fin k)) a = a := rfl
    have hB : baseWordValueLSD ([] : List (Fin k)) = 0 := rfl
    rw [hA, hB]; exact hu0.symm
  | cons d ds ih =>
    have h1 : baseWordValueLSD (d :: ds) = d.val + k * baseWordValueLSD ds := rfl
    change ((fun s => (f s).getD ↑d a) ∘ morphComp f a ds) a = _
    simp only [Function.comp_apply]
    rw [h1, ih, hblock _ _ d.is_lt, add_comm (k * baseWordValueLSD ds)]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[foldlEq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/CobhamUniformMorphism.lean)
-/
@[path]
private lemma foldlEq {q k q' : Nat} (f : Fin q → List (Fin q)) (a : Fin q)
  (e : (Fin q → Fin q) ≃ Fin q')
  (ds : List (Fin k)) (F : Fin q → Fin q) :
  ds.foldl (autoTrans f a e) (e F) = e (F ∘ morphComp f a ds) := by
  induction ds generalizing F with
  | nil => simp [morphComp]
  | cons d ds ih =>
    rw [List.foldl_cons]
    simp only [autoTrans]
    rw [Equiv.symm_apply_apply, ih]
    have hC : morphComp f a (d :: ds) =
      (fun s => (f s).getD ↑d a) ∘ morphComp f a ds := by
      simp only [morphComp, List.foldr_cons]
    rw [hC, Function.comp_assoc]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[auto_of_morphic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/CobhamUniformMorphism.lean)
-/
@[path]
private lemma auto_of_morphic {B : Type} [Fintype B] {k : Nat} (w : Nat → B)
  (h : IsCodingOfProlongableKUniformFixedPoint k w) :
  IsKAutomaticSequence k w := by
  obtain ⟨hk, q, _hq, f, _hlen, a, _tl, _htl, _hfa, u, hu0, hblock, g, hg⟩ := h
  classical
  refine ⟨hk, Fintype.card (Fin q → Fin q), Fintype.card_pos_iff.mpr ⟨id⟩,
    Fintype.equivFin (Fin q → Fin q) id,
    autoTrans f a (Fintype.equivFin (Fin q → Fin q)),
    fun G => g ((Fintype.equivFin (Fin q → Fin q)).symm G a), ?_⟩
  intro n ds hds
  have hfold := foldlEq f a (Fintype.equivFin (Fin q → Fin q)) ds id
  have hC := morphComp_val f a u hu0 hblock ds
  rw [hds] at hC
  change g ((Fintype.equivFin (Fin q → Fin q)).symm
    (ds.foldl (autoTrans f a (Fintype.equivFin (Fin q → Fin q)))
      (Fintype.equivFin (Fin q → Fin q) id)) a) = w n
  simp only [hfold, Equiv.symm_apply_apply, Function.comp_apply, id_eq]
  rw [hC, hg n]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[imgAbove_none](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/CobhamUniformMorphism.lean)
-/
@[path]
private lemma imgAbove_none {q k : Nat} (trans : Fin q → Fin k → Fin q)
  (d : Fin k) :
  imgAbove trans Option.none d =
    if d.val = 0 then Option.none else Option.some (transFn trans d) :=
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[imgAbove_some](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/CobhamUniformMorphism.lean)
-/
@[path]
private lemma imgAbove_some {q k : Nat} (trans : Fin q → Fin k → Fin q)
  (F : Fin q → Fin q) (d : Fin k) :
  imgAbove trans (Option.some F) d = Option.some (F ∘ transFn trans d) :=
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ofFn_getD](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/CobhamUniformMorphism.lean)
-/
@[path]
private lemma ofFn_getD {n : Nat} {α : Type} (f : Fin n → α) (j : Nat) (hj : j < n)
  (d : α) :
  (List.ofFn f).getD j d = f ⟨j, hj⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_ofFn]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[morphImg_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/CobhamUniformMorphism.lean)
-/
@[path]
private lemma morphImg_eq {q k q' : Nat} (trans : Fin q → Fin k → Fin q)
  (e : Option (Fin q → Fin q) ≃ Fin q') (G : Fin q') :
  morphImg trans e G =
    List.ofFn (fun d : Fin k => e (imgAbove trans (e.symm G) d)) :=
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[morphFix_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/CobhamUniformMorphism.lean)
-/
@[path]
private lemma morphFix_zero {q k q' : Nat} (trans : Fin q → Fin k → Fin q)
  (hk : 2 ≤ k) (e : Option (Fin q → Fin q) ≃ Fin q') :
  morphFix trans hk e 0 = e Option.none :=
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[morphFix_ne](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/CobhamUniformMorphism.lean)
-/
@[path]
private lemma morphFix_ne {q k q' : Nat} (trans : Fin q → Fin k → Fin q)
  (hk : 2 ≤ k) (e : Option (Fin q → Fin q) ≃ Fin q') (n : Nat)
  (hne : n ≠ 0) :
  morphFix trans hk e n =
    e (Option.some (fun s => runFrom trans s (repList hk n))) := by
  simp only [morphFix, ite_eq_right hne]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[blockLaw](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/CobhamUniformMorphism.lean)
-/
@[path]
private lemma blockLaw {q k q' : Nat} (trans : Fin q → Fin k → Fin q) (hk : 2 ≤ k)
  (e : Option (Fin q → Fin q) ≃ Fin q') (n j : Nat) (hj : j < k) :
  (morphImg trans e (morphFix trans hk e n)).getD j (e Option.none)
    = morphFix trans hk e (k * n + j) := by
  have hget : (morphImg trans e (morphFix trans hk e n)).getD j (e Option.none)
    = e (imgAbove trans (e.symm (morphFix trans hk e n)) ⟨j, hj⟩) := by
    rw [morphImg_eq]
    exact ofFn_getD _ j hj _
  rw [hget]
  by_cases hn : n = 0
  · subst hn
    have hs : e.symm (morphFix trans hk e 0) = Option.none := by
      rw [morphFix_zero, Equiv.symm_apply_apply]
    rw [hs]
    by_cases hj0 : j = 0
    · subst hj0
      have hi : ∀ d : Fin k, d.val = 0 →
        imgAbove trans Option.none d = Option.none := by
        intro d hd
        rw [imgAbove_none, ite_eq_left hd]
      have hkj : k * 0 + 0 = 0 := by omega
      rw [hi _ rfl, hkj, morphFix_zero]
    · have hi2 : imgAbove trans Option.none ⟨j, hj⟩ =
      Option.some (transFn trans ⟨j, hj⟩) := by
      have hj0' : (⟨j, hj⟩ : Fin k).val ≠ 0 := hj0
      rw [imgAbove_none, ite_eq_right hj0']
      have hkj : k * 0 + j = j := by omega
      have hrep : repList hk j = [⟨j, hj⟩] := by
        have h0 : k * 0 + j ≠ 0 := by omega
        have h1 := repCons hk 0 j hj h0
        rwa [hkj, repList.eq_1 hk] at h1
      rw [hi2, hkj, morphFix_ne trans hk e j hj0, hrep]
      apply congrArg e
      apply congrArg Option.some
      funext s
      rfl
  · have hs : e.symm (morphFix trans hk e n)
    = Option.some (fun s => runFrom trans s (repList hk n)) := by
    rw [morphFix_ne trans hk e n hn, Equiv.symm_apply_apply]
    rw [hs, imgAbove_some]
    have hne : k * n + j ≠ 0 := by
      intro hcon
      have hkn : k * n = 0 := by omega
      obtain hk0 | hn0 := Nat.mul_eq_zero.mp hkn
      · omega
      · exact hn hn0
    rw [morphFix_ne trans hk e (k * n + j) hne, repCons hk n j hj hne]
    apply congrArg e
    apply congrArg Option.some
    funext s
    rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[morphImg_prol](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/CobhamUniformMorphism.lean)
-/
@[path]
private lemma morphImg_prol {q k q' : Nat} (trans : Fin q → Fin k → Fin q)
  (hk : 2 ≤ k) (e : Option (Fin q → Fin q) ≃ Fin q') :
  ∃ tl : List (Fin q'), tl ≠ [] ∧
    morphImg trans e (e Option.none) = e Option.none :: tl := by
  have hL : (morphImg trans e (e Option.none)).length = k := by
    rw [morphImg_eq, List.length_ofFn]
  have hnil : morphImg trans e (e Option.none) ≠ [] := by
    rw [List.ne_nil_iff_length_pos, hL]
    omega
  refine ⟨(morphImg trans e (e Option.none)).tail, ?_, ?_⟩
  · rw [List.ne_nil_iff_length_pos, List.length_tail, hL]
    omega
  · have hhead : (morphImg trans e (e Option.none)).head hnil
    = e Option.none := by
    have h0 : ∀ d : Fin k, d.val = 0 →
      e (imgAbove trans Option.none d) = e Option.none := by
      intro d hd
      rw [imgAbove_none, ite_eq_left hd]
    have hnil' : List.ofFn
      (fun d : Fin k => e (imgAbove trans (e.symm (e Option.none)) d))
        ≠ [] := hnil
    have h1 : (morphImg trans e (e Option.none)).head hnil =
      (fun d : Fin k => e (imgAbove trans (e.symm (e Option.none)) d))
        ⟨0, by omega⟩ := List.head_ofFn hnil'
    rw [h1]
    change e (imgAbove trans (e.symm (e Option.none)) _) = e Option.none
    rw [Equiv.symm_apply_apply]
    exact h0 _ rfl
    have hcons := List.cons_head_tail hnil
    rwa [hhead] at hcons

end MetaMathlibExt

namespace MetaMathlibExt

/--
[morphic_of_auto](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/CobhamUniformMorphism.lean)
-/
@[path]
private lemma morphic_of_auto {B : Type} [Fintype B] {k : Nat} (w : Nat → B)
  (h : IsKAutomaticSequence k w) :
  IsCodingOfProlongableKUniformFixedPoint k w := by
  obtain ⟨hk, q, _hq, start, trans, out, hauto⟩ := h
  classical
  have hlen : ∀ G : Fin (Fintype.card (Option (Fin q → Fin q))),
    (morphImg trans (Fintype.equivFin (Option (Fin q → Fin q))) G).length
      = k := by
    intro G
    rw [morphImg_eq, List.length_ofFn]
  obtain ⟨tl, htl, hfa⟩ :=
    morphImg_prol trans hk (Fintype.equivFin (Option (Fin q → Fin q)))
  refine ⟨hk, Fintype.card (Option (Fin q → Fin q)),
    Fintype.card_pos_iff.mpr ⟨Option.none⟩,
    morphImg trans (Fintype.equivFin (Option (Fin q → Fin q))), hlen,
    Fintype.equivFin (Option (Fin q → Fin q)) Option.none, tl, htl, hfa,
    morphFix trans hk (Fintype.equivFin (Option (Fin q → Fin q))), ?_, ?_, ?_⟩
  · exact morphFix_zero trans hk _
  · intro n j hj
    exact blockLaw trans hk _ n j hj
  · refine ⟨fun G =>
    match (Fintype.equivFin (Option (Fin q → Fin q))).symm G with
    | Option.none => w 0
    | Option.some F => out (F start), ?_⟩
    intro n
    by_cases hn : n = 0
    · subst hn
      rw [morphFix_zero]
      simp only [Equiv.symm_apply_apply]
    · rw [morphFix_ne trans hk _ n hn]
      simp only [Equiv.symm_apply_apply]
      show w n = out (runFrom trans start (repList hk n))
      exact (hauto n (repList hk n) (repVal hk n)).symm
set_option linter.unusedVariables false in

end MetaMathlibExt

namespace MetaMathlibExt

/--
[cobham_automatic_iff_uniform_morphic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/CobhamUniformMorphism.lean)
-/
@[path]
lemma cobham_automatic_iff_uniform_morphic
  [Fintype B]
  {k : Nat}
  {w : Nat → B}
-- given
  (hk : 2 ≤ k) :
-- imply
  IsKAutomaticSequence k w ↔ IsCodingOfProlongableKUniformFixedPoint k w := by
-- proof
  constructor
  · intro h
    exact morphic_of_auto w h
  · intro h
    exact auto_of_morphic w h

end MetaMathlibExt

namespace MetaMathlibExt

/--
[getElem?_flatMap_uniform](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/CobhamUniformMorphism.lean)
-/
@[path]
private lemma getElem?_flatMap_uniform {A : Type*} {k : Nat} {f : A → List A}
  (hlen : ∀ x, (f x).length = k) (l : List A) (m j : Nat) (hj : j < k) :
  (l.flatMap f)[k * m + j]? = l[m]?.bind fun x => (f x)[j]? := by
  induction l generalizing m with
  | nil => simp
  | cons x xs ih =>
    rw [List.flatMap_cons]
    cases m with
    | zero => simp [List.getElem?_append_left (hlen x ▸ hj)]
    | succ m =>
      rw [List.getElem?_append_right (by
        rw [hlen]; exact Nat.le_add_right_of_le (Nat.le_mul_of_pos_right k (Nat.succ_pos m))),
        hlen, List.getElem?_cons_succ, ← ih]
      congr 1
      rw [Nat.mul_succ]
      omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[flatMap_map_range](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/CobhamUniformMorphism.lean)
-/
@[path]
private lemma flatMap_map_range {q k : Nat} {f : Fin q → List (Fin q)} {a : Fin q}
  {u : Nat → Fin q} (hlen : ∀ x, (f x).length = k)
  (hblock : ∀ n j : Nat, j < k → (f (u n)).getD j a = u (k * n + j)) (m : Nat) :
  ((List.range m).map u).flatMap f = (List.range (k * m)).map u := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hfu : f (u m) = (List.range k).map fun j => u (k * m + j) := by
      refine List.ext_getElem (by simp [hlen]) fun j h1 _ => ?_
      rw [← List.getD_eq_getElem _ a h1, hblock m j (hlen (u m) ▸ h1)]
      simp
    rw [List.range_succ, List.map_append, List.flatMap_append, ih, Nat.mul_succ, List.range_add,
      List.map_append, List.map_map]
    simp [hfu, Function.comp_def]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[isCodingOfProlongableKUniformFixedPoint_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/CobhamUniformMorphism.lean)
-/
@[path]
lemma isCodingOfProlongableKUniformFixedPoint_iff
  [Fintype B]
  {k : Nat}
  {w : Nat → B}
-- given
  (hk : 2 ≤ k) :
-- imply
  IsCodingOfProlongableKUniformFixedPoint k w ↔
    ∃ q : Nat, ∃ f : Fin q → List (Fin q), (∀ x, (f x).length = k) ∧
    ∃ a : Fin q, ∃ u : Nat → Fin q, ∃ g : Fin q → B,
    IsPrefixPreserving f a ∧ IsOmegaLimit f a u ∧ ∀ n, w n = g (u n) := by
-- proof
  constructor
  · rintro ⟨-, q, -, f, hlen, a, tl, htl, hfa, u, hu0, hblock, g, hg⟩
    have hL : ∀ n, morphIterate f n [a] = (List.range (k ^ n)).map u := by
      intro n
      induction n with
      | zero => simp [morphIterate, hu0]
      | succ n ih =>
        rw [morphIterate, ih, morphExtend, flatMap_map_range hlen hblock, pow_succ, mul_comm]
    refine ⟨q, f, hlen, a, u, g, ⟨tl, hfa, fun n => ?_⟩, ⟨fun M => ⟨M, ?_⟩, fun n i h => ?_⟩, hg⟩
    · rw [← List.length_pos_iff, morphIterate_length_of_uniform hlen]
      exact Nat.mul_pos (Nat.pow_pos (by omega)) (List.length_pos_iff.2 htl)
    · rw [hL, List.length_map, List.length_range]
      exact (Nat.lt_pow_self hk).le
    · simp [hL]
  · rintro ⟨q, f, hlen, a, u, g, ⟨tl, hfa, -⟩, ⟨-, hlim⟩, hg⟩
    have hL : ∀ n, morphIterate f n [a] = (List.range (k ^ n)).map u := fun n =>
      List.ext_getElem (by simp [morphIterate_length_of_uniform hlen]) fun i h1 _ => by
        simp [← hlim n i h1]
    refine ⟨hk, q, Fin.pos a, f, hlen, a, tl, ?_, hfa, u, ?_, fun m j hj => ?_, g, hg⟩
    · rintro rfl
      have := hlen a
      simp [hfa] at this
      omega
    · simpa [morphIterate] using (hlim 0 0 (by simp [morphIterate])).symm
    · have hm : m < k ^ m := Nat.lt_pow_self hk
      have hkm : k * m + j < k ^ (m + 1) := by
        rw [pow_succ, Nat.mul_comm k m]
        calc m * k + j < m * k + k := Nat.add_lt_add_left hj _
          _ = (m + 1) * k := (Nat.succ_mul m k).symm
          _ ≤ k ^ m * k := Nat.mul_le_mul_right k hm
      have key := getElem?_flatMap_uniform hlen (morphIterate f m [a]) m j hj
      rw [← morphExtend, ← morphIterate, hL, hL] at key
      have hj' : (f (u m))[j]? = some (u (k * m + j)) := by simpa [hm, hkm] using key.symm
      rw [List.getD_eq_getElem?_getD, hj']
      rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[IsCodingOfProlongableKUniformFixedPoint.exists_isMorphic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/CobhamUniformMorphism.lean)
-/
@[path]
lemma IsCodingOfProlongableKUniformFixedPoint.exists_isMorphic
  [Fintype B]
  {k : Nat}
  {w : Nat → B}
-- given
  (h : IsCodingOfProlongableKUniformFixedPoint k w) :
-- imply
  ∃ q : Nat, ∃ u : Nat → Fin q, ∃ g : Fin q → B, IsMorphic u g w := by
-- proof
  obtain ⟨q, f, -, a, u, g, hpre, hlim, hg⟩ :=
    (isCodingOfProlongableKUniformFixedPoint_iff w h.1).1 h
  exact ⟨q, u, g, ⟨f, a, hpre, hlim⟩, hg⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[IsKAutomaticSequence.exists_isMorphic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/CobhamUniformMorphism.lean)
-/
@[path]
lemma IsKAutomaticSequence.exists_isMorphic
  [Fintype B]
  {k : Nat}
  {w : Nat → B}
-- given
  (h : IsKAutomaticSequence k w) :
-- imply
  ∃ q : Nat, ∃ u : Nat → Fin q, ∃ g : Fin q → B, IsMorphic u g w :=
-- proof
  ((cobham_automatic_iff_uniform_morphic w h.1).1 h).exists_isMorphic

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-26
