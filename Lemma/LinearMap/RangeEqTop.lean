import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

section
variable {S : Type u} [Ring S]

private lemma length_add_length_eq
  {D : Type v} [AddCommGroup D] [Module S D]
  (N N' : Submodule S D) :
  -- imply
  Module.length S N + Module.length S N' = Module.length S ↥(N ⊓ N') + Module.length S ↥(N ⊔ N') := by
  -- proof
  let f : ↥(N ⊓ N') →ₗ[S] ↥N × ↥N' :=
    LinearMap.prod (Submodule.inclusion inf_le_left) (Submodule.inclusion inf_le_right)
  let g : ↥N × ↥N' →ₗ[S] ↥(N ⊔ N') :=
    (Submodule.inclusion le_sup_left).comp (LinearMap.fst S N N') -
      (Submodule.inclusion le_sup_right).comp (LinearMap.snd S N N')
  have hf : Function.Injective f := fun x y h => by
    have := congrArg Prod.fst h
    apply Submodule.inclusion_injective _ this
  have hg : Function.Surjective g := by
    rintro ⟨z, hz⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Iff.mp Submodule.mem_sup hz
    refine ⟨(⟨a, ha⟩, ⟨-b, neg_mem hb⟩), Subtype.ext ?_⟩
    simp [g]
  have hfg : Function.Exact f g := by
    intro x
    constructor
    ·
      intro hx
      have h0 : ((x.1 : D) - x.2 : D) = 0 := by
        have := congrArg Subtype.val hx
        simpa [g] using this
      have h12 : (x.1 : D) = x.2 := Iff.mp sub_eq_zero h0
      refine ⟨⟨x.1, x.1.2, h12 ▸ x.2.2⟩, Prod.ext (Subtype.ext rfl) (Subtype.ext h12)⟩
    ·
      rintro ⟨y, rfl⟩
      refine Subtype.ext ?_
      simp [f, g]
  rw [← Module.length_prod]
  apply Module.length_eq_add_of_exact f g hf hg hfg

private lemma length_eq_length_ker_add_length_range
  {S₂ : Type u₁} {σ : S →+* S₂} [Ring S₂] [RingHomSurjective σ]
  {D₁ : Type v} [AddCommGroup D₁] [Module S D₁]
  {D₂ : Type u₂} [AddCommGroup D₂] [Module S₂ D₂]
  (g : LinearMap σ D₁ D₂) :
  -- imply
  Module.length S D₁ = Module.length S ↥(LinearMap.ker g) + Module.length S₂ ↥(LinearMap.range g) := by
  -- proof
  rw [Module.length_eq_add_of_exact (LinearMap.ker g).subtype (LinearMap.ker g).mkQ
    (Submodule.subtype_injective _) (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)]
  congr 1
  let e : LinearMap σ (D₁ ⧸ LinearMap.ker g) ↥(LinearMap.range g) :=
    (LinearMap.ker g).liftQ g.rangeRestrict (le_of_eq (LinearMap.ker_rangeRestrict g).symm)
  have he : Function.Bijective e := by
    constructor
    ·
      rw [← LinearMap.ker_eq_bot]
      refine (Submodule.eq_bot_iff _).2 fun x hx => ?_
      induction x using Submodule.Quotient.induction_on
      rename_i x
      rw [LinearMap.mem_ker, Submodule.liftQ_apply] at hx
      have : x ∈ LinearMap.ker g := by
        rw [← LinearMap.ker_rangeRestrict]
        apply hx
      apply (Submodule.Quotient.mk_eq_zero _).2 this
    ·
      intro y
      obtain ⟨x, hx⟩ := LinearMap.surjective_rangeRestrict g y
      refine ⟨Submodule.Quotient.mk x, ?_⟩
      rw [Submodule.liftQ_apply, hx]
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length, Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComapOfBijective e he)]

end

section
variable {S : Type u} [Ring S] {D : Type v} [AddCommGroup D] [Module S D]

private lemma _root_.HondaLength.length_top :
  -- imply
  Module.length S (⊤ : Submodule S D) = Module.length S D :=
  Module.length_top

private lemma eq_top_of_length_eq
  [IsArtinian S D] [IsNoetherian S D]
  {N : Submodule S D}
  (h : Module.length S N = Module.length S D) :
  -- imply
  N = ⊤ := by
  -- proof
  if hN : N = ⊤ then
    apply hN
  else
    apply (Submodule.length_lt hN).ne h

private lemma length_submodule_ne_top
  [IsArtinian S D] [IsNoetherian S D]
  (N : Submodule S D) :
  -- imply
  Module.length S N ≠ ⊤ :=
  Module.length_ne_top

end

section
variable {S : Type u} [CommRing S] {D : Type v} [AddCommGroup D] [Module S D]
variable {σ τ : S →+* S} [RingHomSurjective σ] [RingHomSurjective τ]

private lemma range_sup_eq_top
  [IsArtinian S D] [IsNoetherian S D]
  (F : LinearMap σ D D)
  (V : LinearMap τ D D)
  (ℓ : S)
  (hFV : ∀ x, F (V x) = ℓ • x)
  (L : Submodule S D)
  (sh1 : ∀ x ∈ L, x ∈ LinearMap.range F → ∃ y ∈ L, x = ℓ • y)
  (sh3 : ∀ x ∈ L, V x = 0 → x = 0)
  (hkerF : LinearMap.ker F ≤ LinearMap.range V)
  (htors : ∀ x : D, ℓ • x = 0 → ∃ y ∈ L, ∃ z : D, V z = 0 ∧ y + z = x) :
  -- imply
  LinearMap.range F ⊔ L = ⊤ := by
  -- proof
  classical
  set FD : Submodule S D := LinearMap.range F with hFD
  set VD : Submodule S D := LinearMap.range V with hVD
  set K : Submodule S D := LinearMap.ker F with hK
  set KV : Submodule S D := LinearMap.ker V with hKV
  set mℓ : D →ₗ[S] D := ℓ • LinearMap.id with hmℓ
  have mℓ_apply : ∀ x, mℓ x = ℓ • x := fun x => rfl
  set T : Submodule S D := LinearMap.ker mℓ with hT
  set ℓD : Submodule S D := LinearMap.range mℓ with hℓD
  set ℓL : Submodule S D := L.map mℓ with hℓL
  have hR1 : VD.map F = ℓD := by
    ext x
    simp only [Submodule.mem_map, LinearMap.mem_range, hVD, hℓD, mℓ_apply]
    constructor
    ·
      rintro ⟨_, ⟨z, rfl⟩, rfl⟩
      refine ⟨z, ?_⟩
      apply (hFV z).symm
    ·
      rintro ⟨z, rfl⟩
      refine ⟨V z, ⟨z, rfl⟩, ?_⟩
      apply hFV z
  have hKV_le_T : KV ≤ T := fun z hz => by
    rw [hT, LinearMap.mem_ker, mℓ_apply, ← hFV z, show V z = 0 from hz, map_zero]
  have hR2 : (T ⊓ L) ⊔ KV = T := by
    apply le_antisymm (sup_le inf_le_left hKV_le_T)
    intro x hx
    obtain ⟨y, hyL, z, hz, rfl⟩ := htors x hx
    have hzT : z ∈ T := hKV_le_T hz
    refine Submodule.mem_sup.2 ⟨y, Submodule.mem_inf.2 ⟨?_, hyL⟩, z, hz, rfl⟩
    rw [hT, LinearMap.mem_ker] at hx hzT ⊢
    rw [map_add, hzT, add_zero] at hx
    apply hx
  have hR2' : (T ⊓ L) ⊓ KV = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 fun x hx => ?_
    apply sh3 x hx.1.2 hx.2
  have hR3 : FD ⊓ L = ℓL := by
    apply le_antisymm
    ·
      rintro x ⟨hxF, hxL⟩
      obtain ⟨y, hyL, rfl⟩ := sh1 x hxL hxF
      refine ⟨y, hyL, ?_⟩
      rfl
    ·
      rintro _ ⟨y, hyL, rfl⟩
      refine ⟨?_, L.smul_mem ℓ hyL⟩
      refine ⟨V y, ?_⟩
      apply hFV y
  have hD : Module.length S D ≠ ⊤ := Module.length_ne_top
  have E1 := length_eq_length_ker_add_length_range F
  have E2 := length_eq_length_ker_add_length_range V
  have E3 := length_eq_length_ker_add_length_range mℓ
  rw [← hK, ← hFD] at E1
  rw [← hKV, ← hVD] at E2
  rw [← hT, ← hℓD] at E3
  have E4 : Module.length S L = Module.length S ↥(T ⊓ L) + Module.length S ℓL := by
    rw [length_eq_length_ker_add_length_range (mℓ.domRestrict L), LinearMap.ker_domRestrict, LinearMap.range_domRestrict]
    congr 1
    have : Submodule.comap L.subtype T = Submodule.comap L.subtype (T ⊓ L) := by
      ext x
      simp
    rw [this]
    apply (Submodule.comapSubtypeEquivOfLe inf_le_right).length_eq
  have E5 : Module.length S VD = Module.length S K + Module.length S ℓD := by
    have hrange : LinearMap.range (F.domRestrict VD) = ℓD := by
      rw [← hR1]
      ext x
      simp only [LinearMap.mem_range, LinearMap.domRestrict_apply, Submodule.mem_map]
      constructor
      ·
        rintro ⟨⟨y, hy⟩, rfl⟩
        refine ⟨y, hy, ?_⟩
        rfl
      ·
        rintro ⟨y, hy, rfl⟩
        refine ⟨⟨y, hy⟩, ?_⟩
        rfl
    rw [length_eq_length_ker_add_length_range (F.domRestrict VD), LinearMap.ker_domRestrict, hrange, (Submodule.comapSubtypeEquivOfLe hkerF).length_eq]
  have E6 : Module.length S ↥(T ⊓ L) + Module.length S KV = Module.length S T := by
    have := length_add_length_eq (T ⊓ L) KV
    rw [hR2', hR2, Module.length_bot, zero_add] at this
    apply this
  have E8 : Module.length S FD + Module.length S L = Module.length S ℓL + Module.length S ↥(FD ⊔ L) := by
    rw [← hR3]
    apply length_add_length_eq FD L
  have fin : ∀ N : Submodule S D, Module.length S N ≠ ⊤ := fun N => Module.length_ne_top
  apply eq_top_of_length_eq
  have key : ∀ {a b : ENat}, a ≠ ⊤ → b ≠ ⊤ → a.toNat = b.toNat → a = b := by
    intro a b ha hb h
    rw [← ENat.coe_toNat ha, ← ENat.coe_toNat hb, h]
  refine key (fin _) hD ?_
  have hadd : ∀ N N' : Submodule S D, (Module.length S N + Module.length S N').toNat = (Module.length S N).toNat + (Module.length S N').toNat :=
    fun N N' => ENat.toNat_add (fin N) (fin N')
  have t1 := congrArg ENat.toNat E1
  have t2 := congrArg ENat.toNat E2
  have t3 := congrArg ENat.toNat E3
  have t4 := congrArg ENat.toNat E4
  have t5 := congrArg ENat.toNat E5
  have t6 := congrArg ENat.toNat E6
  have t8 := congrArg ENat.toNat E8
  rw [hadd] at t1 t2 t3 t4 t5 t6 t8
  rw [hadd] at t8
  omega

end

/--
[Deformation_HondaSystem_range_sup_eq_top_of_isArtinian_of_isNoetherian](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Deformation_HondaSystem_range_sup_eq_top_of_isArtinian_of_isNoetherian.lean)
-/
@[path]
private lemma main
  {S : Type u} {D : Type v} [CommRing S] [AddCommGroup D] [Module S D] [IsArtinian S D] [IsNoetherian S D]
  {σ τ : S →+* S} [RingHomSurjective σ] [RingHomSurjective τ]
  (F : LinearMap σ D D)
  (V : LinearMap τ D D)
  (ℓ : S)
  (hFV : ∀ x, F (V x) = ℓ • x)
  (L : Submodule S D)
  (sh1 : ∀ x ∈ L, x ∈ LinearMap.range F → ∃ y ∈ L, x = ℓ • y)
  (sh3 : ∀ x ∈ L, V x = 0 → x = 0)
  (hkerF : LinearMap.ker F ≤ LinearMap.range V)
  (htors : ∀ x : D, ℓ • x = 0 → ∃ y ∈ L, ∃ z : D, V z = 0 ∧ y + z = x) :
  -- imply
  LinearMap.range F ⊔ L = ⊤ :=
  range_sup_eq_top F V ℓ hFV L sh1 sh3 hkerF htors


-- created on 2026-10-20
