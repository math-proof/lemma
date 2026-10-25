import Mathlib
import sympy.Basic
import sympy.atlas.GroupTheory.SchurZassenhaus
open scoped Pointwise
open MulAction MulOpposite Subgroup QuotientGroup Function
open MathlibExt.GroupTheory.SchurZassenhausWanted


namespace Definitions
end Definitions

namespace MathlibExt.GroupTheory.SchurZassenhausWanted

/-- Local copy: atlas `clsC` is private and not visible across modules. -/
private def clsC
  [Group G] (H : Subgroup G) [IsMulCommutative H] [H.FiniteIndex]
  (K : Subgroup G)
-- given
  (hK : H.IsComplement' K) :
-- imply
  H.QuotientDiff :=
-- proof
  ⟦⟨(K : Set G), hK.symm⟩⟧

/--
[stabilizer_clsC](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/SchurZassenhaus.lean)
-/
@[path]
private lemma stabilizer_clsC
  [Group G] [Finite G] (H : Subgroup G) [H.Normal]
  [IsMulCommutative H] (K : Subgroup G)
-- given
  (hH : (Nat.card H).Coprime H.index)
  (hK : H.IsComplement' K) :
-- imply
  stabilizer G (clsC H K hK) = K := by
-- proof
  refine (eq_of_le_of_card_ge ?_ (le_of_eq
      (Nat.eq_of_mul_eq_mul_left Nat.card_pos
        ((isComplement'_stabilizer_of_coprime hH).card_mul_card.trans
          hK.card_mul_card.symm)))).symm
  intro k hk
  have hset : (MulOpposite.op k⁻¹) • (K : Set G) = (K : Set G) := by
    ext x
    simp only [Set.mem_smul_set, smul_eq_mul_unop, MulOpposite.unop_op, SetLike.mem_coe]
    constructor
    ·
      rintro ⟨y, hy, rfl⟩
      exact K.mul_mem hy (K.inv_mem hk)
    ·
      intro hx
      exact ⟨x * k, K.mul_mem hx hk, by group⟩
  rw [mem_stabilizer_iff]
  change Quotient.mk'' _ = Quotient.mk'' _
  congr 1
  exact Subtype.ext hset

/--
[abelian_conj](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/SchurZassenhaus.lean)
-/
@[path]
private lemma abelian_conj
  [Group G] [Finite G] (H : Subgroup G) [H.Normal]
  [IsMulCommutative H] (K₁ K₂ : Subgroup G)
-- given
  (hH : (Nat.card H).Coprime H.index)
  (h₀ : H.IsComplement' K₁)
  (h₁ : H.IsComplement' K₂) :
-- imply
  ∃ g : G, g ∈ H ∧ K₁.map (MulAut.conj g).toMonoidHom = K₂ := by
-- proof
  obtain ⟨h, hh⟩ := exists_smul_eq hH (clsC H K₁ h₀) (clsC H K₂ h₁)
  refine ⟨(h : G), h.2, ?_⟩
  have hg : (h : G) • (clsC H K₁ h₀) = clsC H K₂ h₁ := hh
  have key : stabilizer G (clsC H K₂ h₁) =
      (stabilizer G (clsC H K₁ h₀)).map (MulAut.conj (h : G)).toMonoidHom := by
    rw [← hg, stabilizer_smul_eq_stabilizer_map_conj]
  rwa [stabilizer_clsC H K₁ hH h₀, stabilizer_clsC H K₂ hH h₁, Eq.comm] at key

/--
[card_map_mk'_of_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/SchurZassenhaus.lean)
-/
@[path]
private lemma card_map_mk'_of_disjoint
  [Group G] [Finite G] (K M : Subgroup G) [M.Normal]
-- given
  (h : K ⊓ M = ⊥) :
-- imply
  Nat.card (K.map (QuotientGroup.mk' M)) = Nat.card K := by
-- proof
  have hinj : Set.InjOn (QuotientGroup.mk' M) (K : Set G) := by
    intro x hx y hy hxy
    have hm : x * y⁻¹ ∈ M := by
      have hker : (QuotientGroup.mk' M) (x * y⁻¹) = 1 := by
        rw [map_mul, map_inv, hxy, mul_inv_cancel]
      rwa [← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at hker
    have hmem : x * y⁻¹ ∈ K ⊓ M := ⟨K.mul_mem hx (K.inv_mem hy), hm⟩
    rwa [h, Subgroup.mem_bot, mul_inv_eq_one] at hmem
  change Nat.card ((QuotientGroup.mk' M) '' (K : Set G)) = Nat.card (K : Set G)
  exact Nat.card_image_of_injOn hinj

/--
[isMulComm_map](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/SchurZassenhaus.lean)
-/
@[path]
private lemma isMulComm_map
  [Group G] (N : Subgroup G) [N.Normal] :
-- imply
  IsMulCommutative (N.map (QuotientGroup.mk' (Bracket.bracket N N))) := by
-- proof
  refine ⟨⟨fun x y => Subtype.ext ?_⟩⟩
  obtain ⟨a, ha, hax⟩ := x.2
  obtain ⟨b, hb, hby⟩ := y.2
  rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hax, ← hby, ← map_mul, ← map_mul,
    QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  have hmem := commutator_mem_commutator (N.inv_mem hb) (N.inv_mem ha)
  rw [commutatorElement_def] at hmem
  convert hmem using 1
  group

/--
[map_isComplement](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/SchurZassenhaus.lean)
-/
@[path]
private lemma map_isComplement
  [Group G] [Finite G] (N M K : Subgroup G)
  [N.Normal] [M.Normal]
-- given
  (hMleN : M ≤ N)
  (hN : (Nat.card N).Coprime N.index)
  (hdisj : K ⊓ M = ⊥)
  (h : N.IsComplement' K) :
-- imply
  (N.map (QuotientGroup.mk' M)).IsComplement' (K.map (QuotientGroup.mk' M)) := by
-- proof
  have hcardK : Nat.card (K.map (QuotientGroup.mk' M)) = Nat.card K :=
    card_map_mk'_of_disjoint K M hdisj
  have hNindexK : N.index = Nat.card K := h.symm.index_eq_card
  have hindexN : (N.map (QuotientGroup.mk' M)).index = N.index :=
    index_map_eq N (QuotientGroup.mk'_surjective M) ((QuotientGroup.ker_mk' M).symm ▸ hMleN)
  have hlagr : Nat.card (N.map (QuotientGroup.mk' M)) * (N.map (QuotientGroup.mk' M)).index = Nat.card (G ⧸ M) := Subgroup.card_mul_index _
  have hdvd : Nat.card (N.map (QuotientGroup.mk' M)) ∣ Nat.card N :=
    card_map_dvd N (QuotientGroup.mk' M)
  refine isComplement'_of_coprime ?_ ?_
  · rwa [hcardK, ← hNindexK, ← hindexN]
  ·
    rw [hcardK, ← hNindexK]
    exact hN.coprime_dvd_left hdvd

/--
[quotient_reduce](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/SchurZassenhaus.lean)
-/
@[path]
private lemma quotient_reduce
  [Group G] [Finite G] (N : Subgroup G) [N.Normal] (K₁ K₂ : Subgroup G)
-- given
  (hN : (Nat.card N).Coprime N.index)
  (h₀ : N.IsComplement' K₁)
  (h₁ : N.IsComplement' K₂) :
-- imply
  ∃ n : G, n ∈ N ∧
    (K₁.map (MulAut.conj n).toMonoidHom) ⊔ Bracket.bracket N N =
      K₂ ⊔ Bracket.bracket N N := by
-- proof
  set M : Subgroup G := Bracket.bracket N N with hMdef
  have hMnorm : M.Normal := commutator_normal N N
  have hMleN : M ≤ N := commutator_le_right N N
  have hcard : (Nat.card (N.map (mk' M))).Coprime (N.map (mk' M)).index := by
    rw [index_map_eq N (mk'_surjective M) ((ker_mk' M).symm ▸ hMleN)]
    exact hN.coprime_dvd_left (card_map_dvd N (mk' M))
  have hdisj : ∀ K : Subgroup G, N.IsComplement' K → K ⊓ M = ⊥ := by
    intro K hK
    have hNK : N ⊓ K = ⊥ := disjoint_iff.mp hK.disjoint
    apply le_bot_iff.mp
    calc
      _ ≤ N ⊓ K := le_inf (le_trans inf_le_right hMleN) inf_le_left
      _ = ⊥ := hNK
  have h₀' := map_isComplement N M K₁ hMleN hN (hdisj K₁ h₀) h₀
  have h₁' := map_isComplement N M K₂ hMleN hN (hdisj K₂ h₁) h₁
  have hcomm : IsMulCommutative (N.map (mk' M)) := isMulComm_map N
  obtain ⟨gb, hgbmem, hgbeq⟩ := abelian_conj (N.map (mk' M)) _ _ hcard h₀' h₁'
  obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hgbmem
  refine ⟨n, hn, ?_⟩
  have hcomp : (MulAut.conj ((mk' M) n)).toMonoidHom.comp (mk' M) = (mk' M).comp (MulAut.conj n).toMonoidHom := by
    ext x
    simp [QuotientGroup.mk'_apply]
  have hconj : (K₁.map (mk' M)).map (MulAut.conj ((mk' M) n)).toMonoidHom = (K₁.map (MulAut.conj n).toMonoidHom).map (mk' M) := by
    rw [Subgroup.map_map, Subgroup.map_map, hcomp]
  rw [hconj] at hgbeq
  have hcomap := congrArg (Subgroup.comap (mk' M)) hgbeq
  rwa [Subgroup.comap_map_eq, Subgroup.comap_map_eq, ker_mk'] at hcomap

/--
[conj_preserves_complement](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/SchurZassenhaus.lean)
-/
@[path]
private lemma conj_preserves_complement
  [Group G] [Finite G] (N K : Subgroup G) [hNn : N.Normal]
-- given
  (h : N.IsComplement' K)
  (g : G) :
-- imply
  N.IsComplement' (K.map (MulAut.conj g).toMonoidHom) := by
-- proof
  have hNK : N ⊓ K = ⊥ := disjoint_iff.mp h.disjoint
  have hcard := h.card_mul_card
  apply isComplement'_of_card_mul_and_disjoint
  · rwa [card_map_of_injective (MulAut.conj g).injective]
  ·
    rw [disjoint_iff, eq_bot_iff]
    rintro x ⟨hxN, y, hyK, rfl⟩
    have hyN : y ∈ N := by
      have h2 := hNn.conj_mem _ hxN g⁻¹
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at h2
      have he : g⁻¹ * (g * y * g⁻¹) * g = y := by group
      rwa [he] at h2
    have hyNK : y ∈ N ⊓ K := ⟨hyN, hyK⟩
    rw [hNK, Subgroup.mem_bot] at hyNK
    subst hyNK
    simp

/--
[card_sup_of_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/SchurZassenhaus.lean)
-/
@[path]
private lemma card_sup_of_disjoint
  [Group G] [Finite G] (M K : Subgroup G) [M.Normal]
-- given
  (h : M ⊓ K = ⊥) :
-- imply
  Nat.card (M ⊔ K : Subgroup G) = Nat.card M * Nat.card K := by
-- proof
  have hdisj : Disjoint M K := disjoint_iff.mpr h
  have hinj : Injective (fun p : M × K => (p.1 : G) * (p.2 : G)) :=
    mul_injective_of_disjoint hdisj
  let f : M × K → (M ⊔ K : Subgroup G) :=
    fun p => ⟨(p.1 : G) * (p.2 : G), mul_mem_sup p.1.2 p.2.2⟩
  have hfinj : Injective f := fun a b hab => hinj (by simpa [f, Subtype.ext_iff] using hab)
  have hfsurj : Surjective f := by
    rintro ⟨x, hx⟩
    have hxmul : x ∈ (↑M * ↑K : Set G) := by
      rwa [← Subgroup.normal_mul]
    obtain ⟨m, hm, k, hk, rfl⟩ := hxmul
    exact ⟨(⟨m, hm⟩, ⟨k, hk⟩), by simp [f]⟩
  have hcongr := Nat.card_congr (Equiv.ofBijective f ⟨hfinj, hfsurj⟩)
  rwa [Nat.card_prod, Eq.comm] at hcongr

/--
[subgroupOf_isComplement](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/SchurZassenhaus.lean)
-/
@[path]
private lemma subgroupOf_isComplement
  [Group G] [Finite G] (M K L : Subgroup G) [M.Normal]
-- given
  (hML : M ≤ L)
  (hdisj : M ⊓ K = ⊥)
  (hsup : M ⊔ K = L) :
-- imply
  (M.subgroupOf L).IsComplement' (K.subgroupOf L) := by
-- proof
  have hcardM : Nat.card (M.subgroupOf L) = Nat.card M := by
    have hmp := card_map_of_injective (K := M.subgroupOf L) L.subtype_injective
    rwa [map_subgroupOf_eq_of_le hML, eq_comm] at hmp
  have hKL : K ≤ L := hsup ▸ le_sup_right
  have hcardK : Nat.card (K.subgroupOf L) = Nat.card K := by
    have hmp := card_map_of_injective (K := K.subgroupOf L) L.subtype_injective
    rwa [map_subgroupOf_eq_of_le hKL, eq_comm] at hmp
  apply isComplement'_of_card_mul_and_disjoint
  · rw [hcardM, hcardK, ← card_sup_of_disjoint M K hdisj, hsup]
  ·
    rw [disjoint_iff, eq_bot_iff]
    rintro x ⟨hxM, hxK⟩
    have hx : (x : G) ∈ M ⊓ K := ⟨hxM, hxK⟩
    rw [hdisj, Subgroup.mem_bot] at hx
    rw [Subgroup.mem_bot]
    exact Subtype.ext hx

/--
[conj_subgroupOf_translate](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/SchurZassenhaus.lean)
-/
@[path]
private lemma conj_subgroupOf_translate
  [Group G] (L : Subgroup G) (g' : L) (A : Subgroup G)
-- given
  (hA : A ≤ L) :
-- imply
  map L.subtype ((A.subgroupOf L).map (MulAut.conj g').toMonoidHom) = A.map (MulAut.conj (g' : G)).toMonoidHom := by
-- proof
  have hcomp : L.subtype.comp (MulAut.conj g').toMonoidHom = (MulAut.conj (g' : G)).toMonoidHom.comp L.subtype := by
    ext x
    simp [MulAut.conj_apply, Subgroup.coe_mul]
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr hA]

/--
[solvable_of_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/SchurZassenhaus.lean)
-/
@[path]
private lemma solvable_of_le
  [Group G] (N M : Subgroup G) [Group.IsSolvable N]
-- given
  (h : M ≤ N) :
-- imply
  Group.IsSolvable M := by
-- proof
  have : Group.IsSolvable (M.subgroupOf N) := inferInstance
  exact Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe h).symm.toMonoidHom) (subgroupOfEquivOfLe h).symm.injective

/--
[commutator_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/SchurZassenhaus.lean)
-/
@[path]
private lemma commutator_lt
  [Group G] [Finite G] (N : Subgroup G) [Group.IsSolvable N]
-- given
  (hN : N ≠ ⊥) :
-- imply
  Bracket.bracket N N < N := by
-- proof
  have : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).mpr hN
  rw [← N.range_subtype, MonoidHom.range_eq_map, ← map_commutator, map_subtype_lt_map_subtype]
  have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial (G := N)
  rwa [commutator_def] at hlt

/--
[szcc_aux](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/SchurZassenhaus.lean)
-/
@[path]
private lemma szcc_aux
  [Group G] [Finite G] (N : Subgroup G)
  [N.Normal] [Group.IsSolvable N] (K₁ K₂ : Subgroup G)
-- given
  (hN : (Nat.card N).Coprime N.index)
  (h₀ : N.IsComplement' K₁)
  (h₁ : N.IsComplement' K₂) :
-- imply
  ∃ g : G, g ∈ N ∧ K₁.map (MulAut.conj g).toMonoidHom = K₂ := by
-- proof
  if hNbot : N = ⊥ then
    subst hNbot
    rw [Subgroup.isComplement'_bot_left] at h₀ h₁
    subst h₀
    subst h₁
    exact ⟨1, Subgroup.one_mem _, by simp⟩
  else
    set M : Subgroup G := Bracket.bracket N N with hMdef
    have hMnorm : M.Normal := commutator_normal N N
    have hMleN : M ≤ N := commutator_le_right N N
    have hMltN : M < N := commutator_lt N hNbot
    obtain ⟨n₀, hn₀, hLeq⟩ := quotient_reduce N K₁ K₂ hN h₀ h₁
    set K1prime : Subgroup G := K₁.map (MulAut.conj n₀).toMonoidHom with hK1primeDef
    have h1prime : N.IsComplement' K1prime := conj_preserves_complement N K₁ h₀ n₀
    set L : Subgroup G := K1prime ⊔ M with hLdef
    have hdisjOf : ∀ K : Subgroup G, N.IsComplement' K → M ⊓ K = ⊥ := by
      intro K hK
      have hNK : N ⊓ K = ⊥ := disjoint_iff.mp hK.disjoint
      apply le_bot_iff.mp
      calc
        _ ≤ N ⊓ K := le_inf (le_trans inf_le_left hMleN) inf_le_right
        _ = ⊥ := hNK
    have hdisj1 : M ⊓ K1prime = ⊥ := hdisjOf K1prime h1prime
    have hdisj2 : M ⊓ K₂ = ⊥ := hdisjOf K₂ h₁
    have hMleL : M ≤ L := le_sup_right
    have hK1primeLeL : K1prime ≤ L := le_sup_left
    have hsup1 : M ⊔ K1prime = L := by rw [sup_comm]
    have hsup2 : M ⊔ K₂ = L :=
      (sup_comm (a := M) (b := K₂)).trans (hLeq.symm.trans hLdef.symm)
    have hK2LeL : K₂ ≤ L := hsup2 ▸ le_sup_right
    have hc1 : (M.subgroupOf L).IsComplement' (K1prime.subgroupOf L) :=
      subgroupOf_isComplement M K1prime L hMleL hdisj1 hsup1
    have hc2 : (M.subgroupOf L).IsComplement' (K₂.subgroupOf L) :=
      subgroupOf_isComplement M K₂ L hMleL hdisj2 hsup2
    have hsolvM : Group.IsSolvable M := solvable_of_le N M hMleN
    have : Group.IsSolvable (M.subgroupOf L) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (subgroupOfEquivOfLe hMleL).toMonoidHom)
        (subgroupOfEquivOfLe hMleL).injective
    have hcardM : Nat.card (M.subgroupOf L) = Nat.card M := by
      have hmp := card_map_of_injective (K := M.subgroupOf L) L.subtype_injective
      rwa [map_subgroupOf_eq_of_le hMleL, eq_comm] at hmp
    have hindexM : (M.subgroupOf L).index = Nat.card (K1prime.subgroupOf L) :=
      hc1.symm.index_eq_card
    have hcardK1prime : Nat.card (K1prime.subgroupOf L) = Nat.card K₁ := by
      have h1 : Nat.card (K1prime.subgroupOf L) = Nat.card K1prime := by
        have hmp := card_map_of_injective (K := K1prime.subgroupOf L) L.subtype_injective
        rwa [map_subgroupOf_eq_of_le hK1primeLeL, eq_comm] at hmp
      rw [h1, hK1primeDef, card_map_of_injective (MulAut.conj n₀).injective]
    have hcop : (Nat.card (M.subgroupOf L)).Coprime (M.subgroupOf L).index := by
      rw [hcardM, hindexM, hcardK1prime, ← h₀.symm.index_eq_card]
      exact hN.coprime_dvd_left (Subgroup.card_dvd_of_le hMleN)
    have hcardL : Nat.card L < Nat.card G := by
      have hLcard : Nat.card L = Nat.card M * Nat.card K₁ := by
        rw [← hsup1, card_sup_of_disjoint M K1prime hdisj1, hK1primeDef,
          card_map_of_injective (MulAut.conj n₀).injective]
      have hGcard : Nat.card N * Nat.card K₁ = Nat.card G := h₀.card_mul_card
      rw [hLcard, ← hGcard]
      exact (Nat.mul_lt_mul_right Nat.card_pos).mpr (Subgroup.card_lt_of_lt hMltN)
    obtain ⟨gprime, hgprime, hgeq⟩ :=
      szcc_aux (M.subgroupOf L) (K1prime.subgroupOf L) (K₂.subgroupOf L) hcop hc1 hc2
    have htrans := congrArg (Subgroup.map L.subtype) hgeq
    rw [conj_subgroupOf_translate L gprime K1prime hK1primeLeL,
      map_subgroupOf_eq_of_le hK2LeL] at htrans
    have hgprimeM : (gprime : G) ∈ M := by
      have hmem := (Subgroup.mem_subgroupOf).mp hgprime
      simpa using hmem
    refine ⟨(gprime : G) * n₀, N.mul_mem (hMleN hgprimeM) hn₀, ?_⟩
    have hconjcomp : (MulAut.conj ((gprime : G) * n₀)).toMonoidHom = (MulAut.conj (gprime : G)).toMonoidHom.comp (MulAut.conj n₀).toMonoidHom := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rwa [hconjcomp, ← Subgroup.map_map]
termination_by Nat.card G

/--
[schur_zassenhaus_conjugate_complements](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/SchurZassenhaus.lean)
-/
@[path]
private lemma schur_zassenhaus_conjugate_complements
  [Group G] [Finite G]
  {N : Subgroup G} [N.Normal] [Group.IsSolvable N]
  {K₁ K₂ : Subgroup G}
-- given
  (hN : (Nat.card N).Coprime N.index)
  (h₀ : N.IsComplement' K₁)
  (h₁ : N.IsComplement' K₂) :
-- imply
  ∃ g : G, g ∈ N ∧ K₁.map (MulAut.conj g).toMonoidHom = K₂ :=
-- proof
  szcc_aux N K₁ K₂ hN h₀ h₁

end MathlibExt.GroupTheory.SchurZassenhausWanted


-- created on 2026-10-20
-- updated on 2026-10-24
