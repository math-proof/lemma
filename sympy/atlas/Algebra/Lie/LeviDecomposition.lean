/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Algebra.Lie.Semisimple.Defs

import Mathlib.Algebra.Lie.CartanCriterion
import Mathlib.Algebra.Lie.Quotient
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# Levi decomposition

This file proves Weyl's complete reducibility theorem and the Levi decomposition for
finite-dimensional Lie algebras over fields of characteristic zero.
-/

namespace MathlibExt.Algebra.Lie.LandmarkWanted

open LieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

private noncomputable def leviTraceKernel
    {K L M : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    [Module.Finite K M] : LieIdeal K L where
  __ := LinearMap.ker (LieModule.traceForm K L M)
  lie_mem := by
    intro x y hy
    change LieModule.traceForm K L M ⁅x, y⁆ = 0
    ext z
    rw [LieModule.traceForm_apply_lie_apply']
    have h := LinearMap.congr_fun (LinearMap.mem_ker.mp hy) (⁅x, z⁆ : L)
    simpa using h

private noncomputable def leviCasimir
    {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [Module.Finite K L] [AddCommGroup M] [Module K M] [LieRingModule L M]
    [LieModule K L M] [Module.Free K M] [Module.Finite K M]
    (hβ : (LieModule.traceForm K L M).Nondegenerate) : Module.End K M := by
  classical
  let b := Module.Free.chooseBasis K L
  exact ∑ i, LieModule.toEnd K L M (b i) *
    LieModule.toEnd K L M ((LieModule.traceForm K L M).dualBasis hβ b i)

private def leviZeroFitting
    {K L M : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    (c : Module.End K M)
    (hc : ∀ x : L, Commute c (LieModule.toEnd K L M x)) : LieSubmodule K L M where
  __ := c.maxGenEigenspace 0
  lie_mem := by
    intro x m hm
    exact Module.End.mapsTo_maxGenEigenspace_of_comm (hc x) 0 hm

private def leviHomVanishing
    {K L M : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    (W : LieSubmodule K L M) : LieSubmodule K L (M →ₗ[K] W) where
  carrier := {f | ∀ w : W, f w = 0}
  zero_mem' w := rfl
  add_mem' {f g} hf hg w := by rw [LinearMap.add_apply, hf, hg, add_zero]
  smul_mem' a f hf w := by rw [LinearMap.smul_apply, hf, smul_zero]
  lie_mem := by
    intro x f hf w
    rw [LieHom.lie_apply]
    rw [hf, lie_zero]
    have hfw := hf (⟨⁅x, w.1⁆, W.lie_mem w.2⟩ : W)
    simpa using hfw

private def leviHomScalarMaps
    {K L M : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    (W : LieSubmodule K L M) : LieSubmodule K L (M →ₗ[K] W) where
  carrier := {f | ∃ a : K, ∀ w : W, f w = a • w}
  zero_mem' := ⟨0, fun w ↦ by simp⟩
  add_mem' {f g} := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a + b, fun w ↦ ?_⟩
    rw [LinearMap.add_apply, ha, hb, add_smul]
  smul_mem' c f := by
    rintro ⟨a, ha⟩
    refine ⟨c * a, fun w ↦ ?_⟩
    rw [LinearMap.smul_apply, ha, mul_smul]
  lie_mem := by
    intro x f hf
    obtain ⟨a, ha⟩ := hf
    refine ⟨0, fun w ↦ ?_⟩
    rw [LieHom.lie_apply, ha, lie_smul]
    have haw := ha (⟨⁅x, w.1⁆, W.lie_mem w.2⟩ : W)
    rw [haw]
    have hxw : ⁅x, w⁆ = (⟨⁅x, w.1⁆, W.lie_mem w.2⟩ : W) := rfl
    rw [hxw, sub_self, zero_smul]

private theorem levi_scalar_unique
    {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    (W : LieSubmodule K L M) (hW : W ≠ ⊥) {a b : K}
    (h : ∀ w : W, a • w = b • w) : a = b := by
  have hWsub : W.toSubmodule ≠ ⊥ := by
    intro h
    apply hW
    rw [← LieSubmodule.toSubmodule_inj]
    exact h
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWsub
  have hab : a • w = b • w := congrArg Subtype.val (h ⟨w, hw⟩)
  have hz : (a - b) • w = 0 := by rw [sub_smul, hab, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right hw0)

private noncomputable def leviHomScalar
    {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    (W : LieSubmodule K L M) (hW : W ≠ ⊥) :
    leviHomScalarMaps W →ₗ[K] K where
  toFun f := Classical.choose f.2
  map_add' f g := by
    apply levi_scalar_unique W hW
    intro w
    calc
      Classical.choose (f + g).property • w = (f + g : M →ₗ[K] W) w :=
        (Classical.choose_spec (f + g).property w).symm
      _ = f.1 w + g.1 w := rfl
      _ = Classical.choose f.property • w + Classical.choose g.property • w := by
        rw [Classical.choose_spec f.property w, Classical.choose_spec g.property w]
      _ = (Classical.choose f.property + Classical.choose g.property) • w :=
        (add_smul _ _ _).symm
  map_smul' c f := by
    apply levi_scalar_unique W hW
    intro w
    calc
      Classical.choose (c • f).property • w = (c • f : M →ₗ[K] W) w :=
        (Classical.choose_spec (c • f).property w).symm
      _ = c • f.1 w := rfl
      _ = c • (Classical.choose f.property • w) := by
        rw [Classical.choose_spec f.property w]
      _ = (c * Classical.choose f.property) • w := (mul_smul _ _ _).symm

private theorem leviHomScalar_ker
    {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    (W : LieSubmodule K L M) (hW : W ≠ ⊥) :
    LinearMap.ker (leviHomScalar W hW) =
      (leviHomVanishing W).toSubmodule.comap
        (leviHomScalarMaps W).toSubmodule.subtype := by
  ext f
  constructor
  · intro hf
    change leviHomScalar W hW f = 0 at hf
    change ∀ w : W, f.1 w = 0
    intro w
    rw [leviHomScalar_apply W hW f w, hf, zero_smul]
  · intro hf
    change leviHomScalar W hW f = 0
    apply levi_scalar_unique W hW
    intro w
    rw [zero_smul]
    exact (leviHomScalar_apply W hW f w).symm.trans (hf w)

private theorem leviHomScalar_surjective
    {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    (W : LieSubmodule K L M) (hW : W ≠ ⊥) :
    Function.Surjective (leviHomScalar W hW) := by
  obtain ⟨Q, hQ⟩ := W.toSubmodule.exists_isCompl
  let p : M →ₗ[K] W := W.toSubmodule.projectionOnto Q hQ
  have hp (w : W) : p w = w := by
    exact Submodule.projectionOnto_apply_left hQ w
  let pv : leviHomScalarMaps W :=
    ⟨p, 1, fun w ↦ by rw [hp, one_smul]⟩
  have hpv : leviHomScalar W hW pv = 1 := by
    apply levi_scalar_unique W hW
    intro w
    rw [one_smul]
    exact (leviHomScalar_apply W hW pv w).symm.trans (hp w)
  intro a
  refine ⟨a • pv, ?_⟩
  rw [LinearMap.map_smul, hpv, smul_eq_mul, mul_one]

private theorem leviHomScalarMaps_quotient_finrank
    {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    [Module.Finite K M] (W : LieSubmodule K L M) (hW : W ≠ ⊥) :
    Module.finrank K
        (leviHomScalarMaps W ⧸
          (leviHomVanishing W).comap (leviHomScalarMaps W).incl) = 1 := by
  let s := leviHomScalar W hW
  have hsKer : LinearMap.ker s =
      ((leviHomVanishing W).comap (leviHomScalarMaps W).incl).toSubmodule := by
    exact leviHomScalar_ker W hW
  have hsRange : LinearMap.range s = ⊤ :=
    LinearMap.range_eq_top.mpr (leviHomScalar_surjective W hW)
  change Module.finrank K
      (leviHomScalarMaps W ⧸
        ((leviHomVanishing W).comap (leviHomScalarMaps W).incl).toSubmodule) = 1
  rw [← hsKer, s.quotKerEquivRange.finrank_eq, hsRange]
  rw [finrank_top]
  exact Module.finrank_self K

/-- Weyl's complete reducibility theorem for finite-dimensional modules over a
semisimple Lie algebra in characteristic zero. -/
theorem _root_.LieModule.exists_isCompl_of_isSemisimple
    {K L M : Type*} [Field K] [CharZero K] [LieRing L]
    [LieAlgebra K L] [Module.Finite K L] [LieAlgebra.IsSemisimple K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    [Module.Finite K M] (W : LieSubmodule K L M) :
    ∃ U : LieSubmodule K L M, IsCompl W U := by
  by_cases hW : W = ⊥
  · subst W
    exact ⟨⊤, isCompl_bot_top⟩
  let V := leviHomScalarMaps W
  let Z := (leviHomVanishing W).comap V.incl
  have hfin : Module.finrank K (V ⧸ Z) = 1 :=
    leviHomScalarMaps_quotient_finrank W hW
  obtain ⟨T, hT⟩ := levi_codim_one_complement Z hfin
  obtain ⟨Q, hQ⟩ := W.toSubmodule.exists_isCompl
  let p : M →ₗ[K] W := W.toSubmodule.projectionOnto Q hQ
  have hp (w : W) : p w = w := Submodule.projectionOnto_apply_left hQ w
  let pv : V := ⟨p, 1, fun w ↦ by rw [hp, one_smul]⟩
  have hpvScalar : leviHomScalar W hW pv = 1 := by
    apply levi_scalar_unique W hW
    intro w
    rw [one_smul]
    exact (leviHomScalar_apply W hW pv w).symm.trans (hp w)
  have hpvMem : pv ∈ Z ⊔ T := by
    rw [hT.sup_eq_top]
    trivial
  rw [LieSubmodule.mem_sup] at hpvMem
  obtain ⟨z, hz, t, ht, hzt⟩ := hpvMem
  have hzScalar : leviHomScalar W hW z = 0 := by
    have hzKer : z ∈ LinearMap.ker (leviHomScalar W hW) := by
      rw [leviHomScalar_ker W hW]
      exact hz
    exact hzKer
  have htScalar : leviHomScalar W hW t = 1 := by
    have h := congrArg (fun f : V ↦ leviHomScalar W hW f) hzt
    rw [LinearMap.map_add, hzScalar, zero_add, hpvScalar] at h
    exact h
  have htApply (w : W) : t.1 w = w := by
    rw [leviHomScalar_apply W hW t w, htScalar, one_smul]
  have htInvariant (x : L) : ⁅x, (t.1 : M →ₗ[K] W)⁆ = 0 := by
    have hxZ : ⁅x, t⁆ ∈ Z := by
      exact levi_lie_mem_HomVanishing_of_mem_scalarMaps W t x
    have hxT : ⁅x, t⁆ ∈ T := T.lie_mem ht
    have hxBot : ⁅x, t⁆ ∈ (⊥ : LieSubmodule K L V) := by
      rw [← hT.inf_eq_bot]
      exact ⟨hxZ, hxT⟩
    have hxZero : ⁅x, t⁆ = 0 := by simpa using hxBot
    exact congrArg Subtype.val hxZero
  let U : LieSubmodule K L M :=
    { carrier := {m | t.1 m = 0}
      zero_mem' := LinearMap.map_zero t.1
      add_mem' := by
        intro a b ha hb
        change t.1 (a + b) = 0
        rw [LinearMap.map_add, ha, hb, add_zero]
      smul_mem' := by
        intro a m hm
        change t.1 (a • m) = 0
        rw [LinearMap.map_smul, hm, smul_zero]
      lie_mem := by
        intro x m hm
        have h := congrArg (fun f : M →ₗ[K] W ↦ f m) (htInvariant x)
        rw [LieHom.lie_apply, hm, lie_zero, zero_sub] at h
        exact neg_eq_zero.mp h }
  refine ⟨U, ?_⟩
  constructor
  · rw [disjoint_iff, eq_bot_iff]
    intro m hm
    have htm : t.1 m = 0 := hm.2
    have hrest := htApply (⟨m, hm.1⟩ : W)
    have hm0 : m = 0 := by
      have h := congrArg Subtype.val hrest
      rw [htm] at h
      exact h.symm
    change m = 0
    exact hm0
  · rw [codisjoint_iff, eq_top_iff]
    intro m _
    rw [LieSubmodule.mem_sup]
    refine ⟨(t.1 m).1, (t.1 m).2, m - (t.1 m).1, ?_, ?_⟩
    · change t.1 (m - (t.1 m).1) = 0
      rw [LinearMap.map_sub, htApply (t.1 m), sub_self]
    · abel

private noncomputable def leviFactorAction
    {K L M : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    (I : LieIdeal K L) (hI : ∀ x ∈ I, ∀ m : M, ⁅x, m⁆ = 0) :
    (L ⧸ I) →ₗ⁅K⁆ Module.End K M := by
  let f := LieModule.toEnd K L M
  have hker : I.toSubmodule ≤ LinearMap.ker (f : L →ₗ[K] Module.End K M) := by
    intro x hx
    rw [LinearMap.mem_ker]
    ext m
    exact hI x hx m
  exact
    { I.toSubmodule.liftQ (f : L →ₗ[K] Module.End K M) hker with
      map_lie' := by
        intro x y
        induction x using Submodule.Quotient.induction_on with
        | _ x =>
          induction y using Submodule.Quotient.induction_on with
          | _ y =>
            rw [← LieSubmodule.Quotient.mk_bracket]
            change f ⁅x, y⁆ = ⁅f x, f y⁆
            exact f.map_lie x y }

@[instance_reducible] private noncomputable def leviFactorLieRingModule
    {K L M : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    (I : LieIdeal K L) (hI : ∀ x ∈ I, ∀ m : M, ⁅x, m⁆ = 0) :
    LieRingModule (L ⧸ I) M :=
  LieRingModule.compLieHom M (leviFactorAction I hI)

private theorem leviFactorAction_mk
    {K L M : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    (I : LieIdeal K L) (hI : ∀ x ∈ I, ∀ m : M, ⁅x, m⁆ = 0)
    (x : L) (m : M) :
    leviFactorAction I hI (LieSubmodule.Quotient.mk x) m = ⁅x, m⁆ := by
  rfl

private noncomputable def leviFactorSubmodule
    {K L M : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    (I : LieIdeal K L) (hI : ∀ x ∈ I, ∀ m : M, ⁅x, m⁆ = 0)
    (W : LieSubmodule K L M) :
    letI := leviFactorLieRingModule I hI
    LieSubmodule K (L ⧸ I) M := by
  letI := leviFactorLieRingModule I hI
  exact
    { W.toSubmodule with
      lie_mem := by
        intro x m hm
        induction x using Submodule.Quotient.induction_on with
        | _ x =>
          change leviFactorAction I hI (LieSubmodule.Quotient.mk x) m ∈ W
          rw [leviFactorAction_mk I hI]
          exact W.lie_mem hm }

private noncomputable def leviUnfactorSubmodule
    {K L M : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    (I : LieIdeal K L) (hI : ∀ x ∈ I, ∀ m : M, ⁅x, m⁆ = 0) :
    letI := leviFactorLieRingModule I hI
    LieSubmodule K (L ⧸ I) M → LieSubmodule K L M := by
  letI := leviFactorLieRingModule I hI
  intro W
  exact
    { W.toSubmodule with
      lie_mem := by
        intro x m hm
        rw [← leviFactorAction_mk I hI]
        exact W.lie_mem hm }

private def leviQuotientMk
    {K L : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    (I : LieIdeal K L) : L →ₗ⁅K⁆ L ⧸ I :=
  { (LieSubmodule.Quotient.mk' I : L →ₗ[K] L ⧸ I) with
    map_lie' := by
      intro x y
      change LieSubmodule.Quotient.mk ⁅x, y⁆ =
        ⁅LieSubmodule.Quotient.mk x, LieSubmodule.Quotient.mk y⁆
      exact LieSubmodule.Quotient.mk_bracket I x y }

@[simp] private theorem leviQuotientMk_apply
    {K L : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    (I : LieIdeal K L) (x : L) :
    leviQuotientMk I x = LieSubmodule.Quotient.mk x := by
  rfl

private def leviComapMap
    {K L L' : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    [LieRing L'] [LieAlgebra K L'] (f : L →ₗ⁅K⁆ L') (J : LieIdeal K L') :
    J.comap f →ₗ⁅K⁆ J where
  toFun x := ⟨f x.1, x.2⟩
  map_add' x y := Subtype.ext (f.map_add x.1 y.1)
  map_smul' c x := Subtype.ext (f.map_smul c x.1)
  map_lie' := by
    intro x y
    apply Subtype.ext
    exact f.map_lie x.1 y.1

private def leviComapMapKerToKer
    {K L L' : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    [LieRing L'] [LieAlgebra K L'] (f : L →ₗ⁅K⁆ L') (J : LieIdeal K L') :
    (leviComapMap f J).ker →ₗ⁅K⁆ f.ker where
  toFun x := ⟨x.1.1, by
    rw [LieHom.mem_ker]
    have hx : leviComapMap f J x.1 = 0 := LieHom.mem_ker.mp x.2
    have h := congrArg Subtype.val hx
    exact h⟩
  map_add' x y := Subtype.ext rfl
  map_smul' c x := Subtype.ext rfl
  map_lie' := by
    intro x y
    apply Subtype.ext
    rfl

private def leviMapRestrict
    {K L L' : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    [LieRing L'] [LieAlgebra K L'] (f : L →ₗ⁅K⁆ L') (I : LieIdeal K L) :
    I →ₗ⁅K⁆ I.map f where
  toFun x := ⟨f x.1, LieIdeal.mem_map x.2⟩
  map_add' x y := Subtype.ext (f.map_add x.1 y.1)
  map_smul' c x := Subtype.ext (f.map_smul c x.1)
  map_lie' := by
    intro x y
    apply Subtype.ext
    exact f.map_lie x.1 y.1

private def leviTheta
    {K L : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    (I : LieIdeal K L) (f : leviHomScalarMaps (L := L) I) :
    I →ₗ[K] leviHomScalarMaps I where
  toFun x := ⁅(x.1 : L), f⁆
  map_add' x y := by rw [Submodule.coe_add, add_lie]
  map_smul' a x := by
    change ⁅((a • x).1 : L), f⁆ = (RingHom.id K) a • ⁅(x.1 : L), f⁆
    rw [RingHom.id_apply, SetLike.val_smul, smul_lie]

private def leviStabilizer
    {K L : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    (I : LieIdeal K L) (f : leviHomScalarMaps (L := L) I) :
    LieSubalgebra K L where
  carrier := {x | ⁅x, f⁆ = 0}
  zero_mem' := by
    change ⁅0, f⁆ = 0
    rw [zero_lie]
  add_mem' {x y} hx hy := by
    change ⁅x + y, f⁆ = 0
    rw [add_lie, hx, hy, add_zero]
  smul_mem' a x hx := by
    change ⁅a • x, f⁆ = 0
    rw [smul_lie, hx, smul_zero]
  lie_mem' := by
    intro x y hx hy
    change ⁅⁅x, y⁆, f⁆ = 0
    rw [lie_lie, hx, hy]
    simp

private def leviSubalgebraComapMap
    {K L G : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    [LieRing G] [LieAlgebra K G] (q : L →ₗ⁅K⁆ G) (T : LieSubalgebra K G) :
    T.comap q →ₗ⁅K⁆ T where
  toFun x := ⟨q x.1, x.2⟩
  map_add' x y := Subtype.ext (q.map_add x.1 y.1)
  map_smul' a x := Subtype.ext (q.map_smul a x.1)
  map_lie' := by
    intro x y
    apply Subtype.ext
    exact q.map_lie x.1 y.1

private def leviSubalgebraComapKerToKer
    {K L G : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    [LieRing G] [LieAlgebra K G] (q : L →ₗ⁅K⁆ G) (T : LieSubalgebra K G) :
    (leviSubalgebraComapMap q T).ker →ₗ⁅K⁆ q.ker where
  toFun x := ⟨x.1.1, by
    rw [LieHom.mem_ker]
    have hx : leviSubalgebraComapMap q T x.1 = 0 := LieHom.mem_ker.mp x.2
    exact congrArg Subtype.val hx⟩
  map_add' x y := Subtype.ext rfl
  map_smul' a x := Subtype.ext rfl
  map_lie' := by
    intro x y
    apply Subtype.ext
    rfl
end MathlibExt.Algebra.Lie.LandmarkWanted
