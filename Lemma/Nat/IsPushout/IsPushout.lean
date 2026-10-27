import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma pb_exists
  {P X Y Z : (CommRingCat : Type (u + 1))}
  {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
  (h : IsPullback fst snd f g)
  (x : X)
  (y : Y)
  -- given
  (hxy : f x = g y) :
  -- imply
  ∃ p : P, fst p = x ∧ snd p = y := by
  -- proof
  let e := h.isLimit.conePointUniqueUpToIso (CommRingCat.pullbackConeIsLimit f g)
  have h1 := h.isLimit.conePointUniqueUpToIso_inv_comp (CommRingCat.pullbackConeIsLimit f g) WalkingCospan.left
  have h2 := h.isLimit.conePointUniqueUpToIso_inv_comp (CommRingCat.pullbackConeIsLimit f g) WalkingCospan.right
  let v : RingHom.eqLocus (f.hom.comp (RingHom.fst X Y)) (g.hom.comp (RingHom.snd X Y)) := ⟨(x, y), hxy⟩
  refine ⟨e.inv v, ?_, ?_⟩
  ·
    have := congrArg (fun k : _ ⟶ X => k v) h1
    simp [CommRingCat.pullbackCone] at this
    apply this
  ·
    have := congrArg (fun k : _ ⟶ Y => k v) h2
    simp [CommRingCat.pullbackCone] at this
    apply this

private lemma pb_ext
  {P X Y Z : (CommRingCat : Type (u + 1))}
  {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
  (h : IsPullback fst snd f g)
  (p q : P)
  -- given
  (hfst : fst p = fst q)
  (hsnd : snd p = snd q) :
  -- imply
  p = q := by
  -- proof
  let e := h.isLimit.conePointUniqueUpToIso (CommRingCat.pullbackConeIsLimit f g)
  have k1 := h.isLimit.conePointUniqueUpToIso_hom_comp (CommRingCat.pullbackConeIsLimit f g) WalkingCospan.left
  have k2 := h.isLimit.conePointUniqueUpToIso_hom_comp (CommRingCat.pullbackConeIsLimit f g) WalkingCospan.right
  apply e.commRingCatIsoToRingEquiv.injective
  have k1p := congrArg (fun k : P ⟶ X => k p) k1
  have k1q := congrArg (fun k : P ⟶ X => k q) k1
  have k2p := congrArg (fun k : P ⟶ Y => k p) k2
  have k2q := congrArg (fun k : P ⟶ Y => k q) k2
  simp only [CommRingCat.pullbackCone, PullbackCone.mk_π_app_left, PullbackCone.mk_π_app_right, CommRingCat.hom_comp,
    CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply] at k1p k1q k2p k2q
  apply Subtype.ext
  apply Prod.ext
  · apply k1p.trans (hfst.trans k1q.symm)
  · apply k2p.trans (hsnd.trans k2q.symm)

private lemma po_surj
  {C C₀ A A₀ : (CommRingCat : Type (u + 1))}
  {φ : C ⟶ C₀} {u : C ⟶ A} {u₀ : C₀ ⟶ A₀} {q : A ⟶ A₀}
  (h : IsPushout φ u u₀ q)
  -- given
  (hφ : Function.Surjective φ) :
  -- imply
  Function.Surjective q := by
  -- proof
  have htop := CommRingCat.closure_range_union_range_eq_top_of_isPushout h
  have hsub : Set.range u₀ ∪ Set.range q ⊆ (q.hom.range : Set A₀) := by
    intro z hz
    obtain ⟨c₀, rfl⟩ | ⟨a, rfl⟩ := hz
    ·
      obtain ⟨c, rfl⟩ := hφ c₀
      refine ⟨u c, ?_⟩
      have := congrArg (fun k : C ⟶ A₀ => k c) h.w
      simpa using this.symm
    · refine ⟨a, rfl⟩
  have hle : Subring.closure (Set.range u₀ ∪ Set.range q) ≤ q.hom.range := Subring.closure_le.mpr hsub
  rw [htop, top_le_iff] at hle
  intro z
  apply hle ▸ Subring.mem_top z

private lemma po_ker
  {C C₀ A A₀ : (CommRingCat : Type (u + 1))}
  {φ : C ⟶ C₀} {u : C ⟶ A} {u₀ : C₀ ⟶ A₀} {q : A ⟶ A₀}
  (h : IsPushout φ u u₀ q)
  -- given
  (hφ : Function.Surjective φ) :
  -- imply
  RingHom.ker q.hom = (RingHom.ker φ.hom).map u.hom := by
  -- proof
  apply le_antisymm
  ·
    set I : Ideal A := (RingHom.ker φ.hom).map u.hom with hI
    have hker : RingHom.ker φ.hom ≤ RingHom.ker ((Ideal.Quotient.mk I).comp u.hom) := by
      intro c hc
      rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      apply Ideal.mem_map_of_mem _ hc
    let c₀ : C₀ →+* A ⧸ I := φ.hom.liftOfSurjective hφ ⟨(Ideal.Quotient.mk I).comp u.hom, hker⟩
    have hc₀ : c₀.comp φ.hom = (Ideal.Quotient.mk I).comp u.hom := RingHom.liftOfSurjective_comp _ hφ _
    have hw : φ ≫ CommRingCat.ofHom c₀ = u ≫ CommRingCat.ofHom (Ideal.Quotient.mk I) := by
      ext c
      apply congrArg (fun k : C →+* A ⧸ I => k c) hc₀
    let d := h.desc (CommRingCat.ofHom c₀) (CommRingCat.ofHom (Ideal.Quotient.mk I)) hw
    have hd : q ≫ d = CommRingCat.ofHom (Ideal.Quotient.mk I) := h.inr_desc _ _ hw
    intro x hx
    rw [RingHom.mem_ker] at hx
    have := congrArg (fun k : A ⟶ CommRingCat.of (A ⧸ I) => k x) hd
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, hx, map_zero, CommRingCat.hom_ofHom] at this
    apply Iff.mp Ideal.Quotient.eq_zero_iff_mem this.symm
  ·
    rw [Ideal.map_le_iff_le_comap]
    intro c hc
    rw [RingHom.mem_ker] at hc
    rw [Ideal.mem_comap, RingHom.mem_ker]
    have := congrArg (fun k : C ⟶ A₀ => k c) h.w
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, hc, map_zero] at this
    apply this.symm

private lemma half
  {P C' C'' C₀ A A' A'' A₀ : (CommRingCat : Type (u + 1))}
  {p' : P ⟶ C'} {p'' : P ⟶ C''} {φ' : C' ⟶ C₀} {φ'' : C'' ⟶ C₀}
  (hC : IsPullback p' p'' φ' φ'')
  {a' : A ⟶ A'} {a'' : A ⟶ A''} {q' : A' ⟶ A₀} {q'' : A'' ⟶ A₀}
  (hA : IsPullback a' a'' q' q'')
  (u : P ⟶ A)
  (u' : C' ⟶ A')
  (u'' : C'' ⟶ A'')
  (u₀ : C₀ ⟶ A₀)
  -- given
  (hu' : p' ≫ u' = u ≫ a')
  (hu'' : p'' ≫ u'' = u ≫ a'')
  (_ : φ' ≫ u₀ = u' ≫ q')
  (_ : φ'' ≫ u₀ = u'' ≫ q'')
  (hφ' : Function.Surjective φ'.hom)
  (hφ'' : Function.Surjective φ''.hom)
  (hco' : IsPushout φ' u' u₀ q')
  (hco'' : IsPushout φ'' u'' u₀ q'') :
  -- imply
  IsPushout p' u u' a' := by
  -- proof
  have hq''s : Function.Surjective q''.hom := po_surj hco'' hφ''
  have hq's : Function.Surjective q'.hom := po_surj hco' hφ'
  have hp's : Function.Surjective p'.hom := by
    intro c'
    obtain ⟨c'', hc''⟩ := hφ'' (φ' c')
    obtain ⟨j, hj, -⟩ := pb_exists hC c' c'' hc''.symm
    refine ⟨j, hj⟩
  have ha's : Function.Surjective a'.hom := by
    intro x'
    obtain ⟨x'', hx''⟩ := hq''s (q' x')
    obtain ⟨x, hx, -⟩ := pb_exists hA x' x'' hx''.symm
    refine ⟨x, hx⟩
  have ha''s : Function.Surjective a''.hom := by
    intro x''
    obtain ⟨x', hx'⟩ := hq's (q'' x'')
    obtain ⟨x, -, hx⟩ := pb_exists hA x' x'' hx'
    refine ⟨x, hx⟩
  have hker : RingHom.ker a'.hom ≤ (RingHom.ker p'.hom).map u.hom := by
    have key : ∀ x'' ∈ (RingHom.ker φ''.hom).map u''.hom, ∃ z ∈ (RingHom.ker p'.hom).map u.hom, a' z = 0 ∧ a'' z = x'' := by
      intro x'' hx''
      refine Submodule.span_induction (p := fun x'' _ => ∃ z ∈ (RingHom.ker p'.hom).map u.hom, a' z = 0 ∧ a'' z = x'') ?_ ?_ ?_ ?_ hx''
      ·
        intro y hy
        obtain ⟨i, hi, rfl⟩ := hy
        obtain ⟨j, hj1, hj2⟩ := pb_exists hC (0 : C') i (by simpa [map_zero] using (Iff.mp RingHom.mem_ker hi).symm)
        refine ⟨u j, Ideal.mem_map_of_mem _ (by rw [RingHom.mem_ker, hj1]), ?_, ?_⟩
        ·
          have := congrArg (fun k : P ⟶ A' => k j) hu'
          simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, hj1, map_zero] at this
          apply this.symm
        ·
          have := congrArg (fun k : P ⟶ A'' => k j) hu''
          simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, hj2] at this
          apply this.symm
      · refine ⟨0, Ideal.zero_mem _, map_zero _, map_zero _⟩
      ·
        intro x y _ _ hzx hwy
        obtain ⟨z, hz, hz1, hz2⟩ := hzx
        obtain ⟨w, hw, hw1, hw2⟩ := hwy
        refine ⟨z + w, Ideal.add_mem _ hz hw, by rw [map_add, hz1, hw1, add_zero], by rw [map_add, hz2, hw2]⟩
      ·
        intro r x _ hzx
        obtain ⟨z, hz, hz1, hz2⟩ := hzx
        obtain ⟨s, rfl⟩ := ha''s r
        refine ⟨s * z, Ideal.mul_mem_left _ _ hz, by rw [map_mul, hz1, mul_zero], by rw [smul_eq_mul, map_mul, hz2]⟩
    intro x hx
    rw [RingHom.mem_ker] at hx
    have hx'' : a'' x ∈ (RingHom.ker φ''.hom).map u''.hom := by
      rw [← po_ker hco'' hφ'', RingHom.mem_ker]
      have := congrArg (fun k : A ⟶ A₀ => k x) hA.w
      simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, hx, map_zero] at this
      apply this.symm
    obtain ⟨z, hz, hz1, hz2⟩ := key _ hx''
    have : x = z := pb_ext hA x z (by rw [hx, hz1]) (by rw [hz2])
    rw [this]
    apply hz
  refine IsPushout.of_isColimit' ⟨hu'⟩ (PushoutCocone.IsColimit.mk hu' (fun s => CommRingCat.ofHom
      (a'.hom.liftOfSurjective ha's ⟨s.inr.hom, hker.trans ?_⟩)) ?_ ?_ ?_)
  ·
    rw [Ideal.map_le_iff_le_comap]
    intro j hj
    rw [RingHom.mem_ker] at hj
    rw [Ideal.mem_comap, RingHom.mem_ker]
    have := congrArg (fun k : P ⟶ s.pt => k j) s.condition
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, hj, map_zero] at this
    apply this.symm
  ·
    intro s
    ext c'
    obtain ⟨j, rfl⟩ := hp's c'
    have h1 := congrArg (fun k : P ⟶ A' => k j) hu'
    have h2 := congrArg (fun k : P ⟶ s.pt => k j) s.condition
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h1 h2
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom, h1,
      RingHom.liftOfSurjective_comp_apply]
    apply h2.symm
  ·
    intro s
    ext x
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom,
      RingHom.liftOfSurjective_comp_apply]
  ·
    intro s m h1 h2
    ext x'
    obtain ⟨x, rfl⟩ := ha's x'
    have := congrArg (fun k : A ⟶ s.pt => k x) h2
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at this
    simp only [CommRingCat.hom_ofHom, RingHom.liftOfSurjective_comp_apply, this]

/--
[CommRingCat_isPushout_of_isPullback_of_isPullback_of_isPushout_of_surjective](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_CommRingCat_isPushout_of_isPullback_of_isPullback_of_isPushout_of_surjective.lean)
-/
@[path]
private lemma main
  {P C' C'' C₀ A A' A'' A₀ : (CommRingCat : Type (u + 1))}
  {p' : P ⟶ C'} {p'' : P ⟶ C''} {φ' : C' ⟶ C₀} {φ'' : C'' ⟶ C₀}
  (hC : IsPullback p' p'' φ' φ'')
  {a' : A ⟶ A'} {a'' : A ⟶ A''} {q' : A' ⟶ A₀} {q'' : A'' ⟶ A₀}
  (hA : IsPullback a' a'' q' q'')
  (u : P ⟶ A)
  (u' : C' ⟶ A')
  (u'' : C'' ⟶ A'')
  (u₀ : C₀ ⟶ A₀)
  -- given
  (hu' : p' ≫ u' = u ≫ a')
  (hu'' : p'' ≫ u'' = u ≫ a'')
  (hq' : φ' ≫ u₀ = u' ≫ q')
  (hq'' : φ'' ≫ u₀ = u'' ≫ q'')
  (hφ' : Function.Surjective φ'.hom)
  (hφ'' : Function.Surjective φ''.hom)
  (hco' : IsPushout φ' u' u₀ q')
  (hco'' : IsPushout φ'' u'' u₀ q'') :
  -- imply
  IsPushout p' u u' a' ∧ IsPushout p'' u u'' a'' := by
  -- proof
  refine ⟨half hC hA u u' u'' u₀ hu' hu'' hq' hq'' hφ' hφ'' hco' hco'',
    half hC.flip hA.flip u u'' u' u₀ hu'' hu' hq'' hq' hφ'' hφ' hco'' hco'⟩


-- created on 2026-10-20
