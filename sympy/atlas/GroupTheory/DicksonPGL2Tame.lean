/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/DicksonPGL2Tame.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.Rank
import Mathlib.GroupTheory.Sylow
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.RepresentationTheory.Maschke
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Simproc.Factors
import Lemma.Nat.AddCardMul_SubCard1.eq.MulCard_QuotientOrbitRelCard
/-!
# Tame finite subgroups of `PGL₂`

This file classifies finite subgroups of `PGL₂` whose order is prime to the
characteristic, using the action on the projective line.
-/

namespace MetaMathlibExt

open scoped BigOperators

private def dicksonExceptional (G X : Type*) [Group G] [MulAction G X] :=
  {x : X // ∃ g : G, g ≠ 1 ∧ g • x = x}

private instance dicksonExceptionalAction (G X : Type*) [Group G] [MulAction G X] :
    MulAction G (dicksonExceptional G X) where
  smul g x := ⟨g • x.1, by
    obtain ⟨h, hh, hx⟩ := x.2
    refine ⟨g * h * g⁻¹, ?_, ?_⟩
    · intro heq
      apply hh
      have := congrArg (fun k : G => g⁻¹ * k * g) heq
      simpa [mul_assoc] using this
    · simp [mul_smul, hx]⟩
  one_smul x := Subtype.ext (one_smul G x.1)
  mul_smul g h x := Subtype.ext (mul_smul g h x.1)

private def dickson_fixedByExceptionalEquiv {G X : Type*} [Group G] [MulAction G X]
    (g : G) (hg : g ≠ 1) :
    MulAction.fixedBy (dicksonExceptional G X) g ≃ MulAction.fixedBy X g where
  toFun x := ⟨x.1.1, congrArg Subtype.val x.2⟩
  invFun x := ⟨⟨x.1, ⟨g, hg, x.2⟩⟩, Subtype.ext x.2⟩
  left_inv x := by ext; rfl
  right_inv x := by ext; rfl
namespace Dickson

private lemma dickson_normalizedLift_exists {F : Type*} [Field F]
    (x : Projectivization F (Fin 2 → F))
    (h : MulAction.stabilizer (Matrix.ProjGenLinGroup (Fin 2) F) x) :
    ∃ A : GL (Fin 2) F,
      Matrix.ProjGenLinGroup.mk A = h.1 ∧
      (↑(Matrix.GeneralLinearGroup.toLin A) : Module.End F (Fin 2 → F)) x.rep = x.rep := by
  obtain ⟨A, hA⟩ := Matrix.ProjGenLinGroup.mk_surjective h.1
  have hfix : Matrix.ProjGenLinGroup.mk A • x = x := by
    rw [hA]
    exact h.2
  rw [← Projectivization.mk_rep x, Projectivization.PGL.mk_smul_mk,
    Projectivization.mk_eq_mk_iff] at hfix
  obtain ⟨u, hu⟩ := hfix
  let B := Matrix.GeneralLinearGroup.scalar (Fin 2) u⁻¹ * A
  refine ⟨B, ?_, ?_⟩
  · simp [B, hA]
  · change Matrix.mulVec (B : Matrix (Fin 2) (Fin 2) F) x.rep = x.rep
    simp only [B, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar]
    rw [← Matrix.mulVec_mulVec]
    have hu' : Matrix.mulVec (A : Matrix (Fin 2) (Fin 2) F) x.rep =
        (u : F) • x.rep := by
      simpa [Units.smul_def, Matrix.smul_eq_mulVec] using hu.symm
    rw [hu']
    ext i
    simp [Matrix.mulVec, Matrix.scalar]

private lemma dickson_normalizedLift_unique {F : Type*} [Field F]
    (x : Projectivization F (Fin 2 → F)) {A B : GL (Fin 2) F}
    (hmk : Matrix.ProjGenLinGroup.mk A = Matrix.ProjGenLinGroup.mk B)
    (hA : (↑(Matrix.GeneralLinearGroup.toLin A) : Module.End F (Fin 2 → F)) x.rep = x.rep)
    (hB : (↑(Matrix.GeneralLinearGroup.toLin B) : Module.End F (Fin 2 → F)) x.rep = x.rep) :
    A = B := by
  obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hmk
  have huv : (u : F) • x.rep = x.rep := by
    have hu' : Matrix.GeneralLinearGroup.scalar (Fin 2) u * A = B := by
      rw [Matrix.GeneralLinearGroup.scalar_commute]
      exact hu
    have happ := congrArg (fun C : GL (Fin 2) F =>
      Matrix.mulVec (C : Matrix (Fin 2) (Fin 2) F) x.rep) hu'
    simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar] at happ
    rw [← Matrix.mulVec_mulVec] at happ
    have hscalar (w : Fin 2 → F) :
        Matrix.mulVec (Matrix.scalar (Fin 2) (u : F)) w = (u : F) • w := by
      ext i
      simp [Matrix.mulVec, Matrix.scalar]
    have hAm : Matrix.mulVec (A : Matrix (Fin 2) (Fin 2) F) x.rep = x.rep := hA
    have hBm : Matrix.mulVec (B : Matrix (Fin 2) (Fin 2) F) x.rep = x.rep := hB
    rw [hscalar, hAm, hBm] at happ
    exact happ
  have hu1 : (u : F) = 1 := by
    apply smul_left_injective F x.rep_nonzero
    simpa using huv
  have huunit : u = 1 := Units.ext hu1
  subst u
  simpa using hu

private noncomputable def dickson_normalizedLiftFun {F : Type*} [Field F]
    (x : Projectivization F (Fin 2 → F))
    (h : MulAction.stabilizer (Matrix.ProjGenLinGroup (Fin 2) F) x) : GL (Fin 2) F :=
  Classical.choose (dickson_normalizedLift_exists x h)

private lemma dickson_normalizedLiftFun_mk {F : Type*} [Field F]
    (x : Projectivization F (Fin 2 → F))
    (h : MulAction.stabilizer (Matrix.ProjGenLinGroup (Fin 2) F) x) :
    Matrix.ProjGenLinGroup.mk (dickson_normalizedLiftFun x h) = h.1 :=
  (Classical.choose_spec (dickson_normalizedLift_exists x h)).1

private lemma dickson_normalizedLiftFun_rep {F : Type*} [Field F]
    (x : Projectivization F (Fin 2 → F))
    (h : MulAction.stabilizer (Matrix.ProjGenLinGroup (Fin 2) F) x) :
    (↑(Matrix.GeneralLinearGroup.toLin (dickson_normalizedLiftFun x h)) :
      Module.End F (Fin 2 → F)) x.rep = x.rep :=
  (Classical.choose_spec (dickson_normalizedLift_exists x h)).2

private noncomputable def dickson_normalizedLift {F : Type*} [Field F]
    (x : Projectivization F (Fin 2 → F)) :
    MulAction.stabilizer (Matrix.ProjGenLinGroup (Fin 2) F) x →* GL (Fin 2) F where
  toFun := dickson_normalizedLiftFun x
  map_one' := by
    apply dickson_normalizedLift_unique x
    · simp [dickson_normalizedLiftFun_mk]
    · exact dickson_normalizedLiftFun_rep x 1
    · simp
  map_mul' h k := by
    apply dickson_normalizedLift_unique x
    · simp [dickson_normalizedLiftFun_mk]
    · exact dickson_normalizedLiftFun_rep x (h * k)
    · change (↑(Matrix.GeneralLinearGroup.toLin
          (dickson_normalizedLiftFun x h * dickson_normalizedLiftFun x k)) :
          Module.End F (Fin 2 → F)) x.rep = x.rep
      rw [map_mul]
      change (↑(Matrix.GeneralLinearGroup.toLin (dickson_normalizedLiftFun x h)) :
          Module.End F (Fin 2 → F))
        ((↑(Matrix.GeneralLinearGroup.toLin (dickson_normalizedLiftFun x k)) :
          Module.End F (Fin 2 → F)) x.rep) = x.rep
      rw [dickson_normalizedLiftFun_rep, dickson_normalizedLiftFun_rep]

private lemma dickson_normalizedLift_mk {F : Type*} [Field F]
    (x : Projectivization F (Fin 2 → F))
    (h : MulAction.stabilizer (Matrix.ProjGenLinGroup (Fin 2) F) x) :
    Matrix.ProjGenLinGroup.mk (dickson_normalizedLift x h) = h.1 :=
  dickson_normalizedLiftFun_mk x h

private lemma dickson_normalizedLift_rep {F : Type*} [Field F]
    (x : Projectivization F (Fin 2 → F))
    (h : MulAction.stabilizer (Matrix.ProjGenLinGroup (Fin 2) F) x) :
    (↑(Matrix.GeneralLinearGroup.toLin (dickson_normalizedLift x h)) :
      Module.End F (Fin 2 → F)) x.rep = x.rep :=
  dickson_normalizedLiftFun_rep x h

private lemma dickson_isCyclic_of_fixed_point {F Q : Type*} [Field F]
    [Group Q] [Finite Q]
    (ι : Q →* Matrix.ProjGenLinGroup (Fin 2) F) (hι : Function.Injective ι)
    (x : Projectivization F (Fin 2 → F)) (hfix : ∀ q : Q, ι q • x = x)
    (hcard : (Nat.card Q : F) ≠ 0) : IsCyclic Q := by
  let j : Q →* MulAction.stabilizer (Matrix.ProjGenLinGroup (Fin 2) F) x := {
    toFun q := ⟨ι q, hfix q⟩
    map_one' := Subtype.ext (map_one ι)
    map_mul' q r := Subtype.ext (map_mul ι q r) }
  let lift : Q →* GL (Fin 2) F := (dickson_normalizedLift x).comp j
  have hlift_mk (q : Q) : Matrix.ProjGenLinGroup.mk (lift q) = ι q := by
    exact dickson_normalizedLift_mk x (j q)
  have hlift_rep (q : Q) :
      (↑(Matrix.GeneralLinearGroup.toLin (lift q)) :
        Module.End F (Fin 2 → F)) x.rep = x.rep := by
    exact dickson_normalizedLift_rep x (j q)
  have hlift_inj : Function.Injective lift := by
    intro q r hqr
    apply hι
    rw [← hlift_mk q, ← hlift_mk r, hqr]
  let ρ : Representation F Q (Fin 2 → F) :=
    (Units.coeHom (Module.End F (Fin 2 → F))).comp
      (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp lift)
  have hρ_rep (q : Q) : ρ q x.rep = x.rep := by
    exact hlift_rep q
  let S : Subrepresentation ρ := {
    toSubmodule := F ∙ x.rep
    apply_mem_toSubmodule q v hv := by
      rw [Submodule.mem_span_singleton] at hv ⊢
      obtain ⟨a, rfl⟩ := hv
      exact ⟨a, by rw [map_smul, hρ_rep]⟩ }
  let _ : NeZero (Nat.card Q : F) := ⟨hcard⟩
  let _ : Representation.IsSemisimpleRepresentation ρ := inferInstance
  obtain ⟨T, hST⟩ := exists_isCompl S
  have hSTsub : IsCompl S.toSubmodule T.toSubmodule := IsCompl.mk
    (by
      have hd : Disjoint S T := hST.disjoint
      rw [disjoint_iff] at hd ⊢
      exact congrArg Subrepresentation.toSubmodule hd)
    (by
      have hc : Codisjoint S T := hST.codisjoint
      rw [codisjoint_iff] at hc ⊢
      exact congrArg Subrepresentation.toSubmodule hc)
  have hdimT : Module.finrank F T.toSubmodule = 1 := by
    have hdim := Submodule.finrank_add_eq_of_isCompl hSTsub
    change Module.finrank F (F ∙ x.rep) + Module.finrank F T.toSubmodule =
      Module.finrank F (Fin 2 → F) at hdim
    rw [finrank_span_singleton x.rep_nonzero, Module.finrank_fin_fun] at hdim
    omega
  have hTbot : T.toSubmodule ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hdimT
    omega
  obtain ⟨w, hwT, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hTbot
  have hspanT : F ∙ w = T.toSubmodule := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le]
      simpa using hwT
    · rw [finrank_span_singleton hw0, hdimT]
  have hρw_mem (q : Q) : ρ q w ∈ T.toSubmodule :=
    T.apply_mem_toSubmodule q hwT
  have hcoeff_exists (q : Q) : ∃ a : F, a • w = ρ q w := by
    rw [← Submodule.mem_span_singleton, hspanT]
    exact hρw_mem q
  let coeff (q : Q) : F := Classical.choose (hcoeff_exists q)
  have hcoeff (q : Q) : coeff q • w = ρ q w :=
    Classical.choose_spec (hcoeff_exists q)
  have hcoeff0 (q : Q) : coeff q ≠ 0 := by
    intro hzero
    have hρzero : ρ q w = 0 := by rw [← hcoeff q, hzero, zero_smul]
    apply hw0
    apply (Matrix.GeneralLinearGroup.toLin (lift q)).toLinearEquiv.injective
    simpa [ρ] using hρzero
  let χ : Q →* Fˣ := {
    toFun q := Units.mk0 (coeff q) (hcoeff0 q)
    map_one' := by
      apply Units.ext
      apply smul_left_injective F hw0
      simpa using hcoeff 1
    map_mul' q r := by
      apply Units.ext
      apply smul_left_injective F hw0
      calc
        (↑(Units.mk0 (coeff (q * r)) (hcoeff0 (q * r))) : F) • w =
            ρ (q * r) w := hcoeff (q * r)
        _ = ρ q (ρ r w) := by rw [map_mul]; rfl
        _ = ρ q (coeff r • w) := by rw [hcoeff r]
        _ = coeff r • ρ q w := map_smul (ρ q) (coeff r) w
        _ = coeff r • coeff q • w := by rw [← hcoeff q]
        _ = (↑(Units.mk0 (coeff q) (hcoeff0 q) *
              Units.mk0 (coeff r) (hcoeff0 r)) : F) • w := by
            simp only [Units.val_mul, Units.val_mk0]
            simp only [smul_smul]
            rw [mul_comm] }
  have hcoeff_lift (q : Q) : coeff q • w =
      (↑(Matrix.GeneralLinearGroup.toLin (lift q)) :
        Module.End F (Fin 2 → F)) w := by
    exact hcoeff q
  have hχinj : Function.Injective χ := by
    intro q r hχ
    apply hlift_inj
    apply Matrix.GeneralLinearGroup.toLin.injective
    apply Units.ext
    apply LinearMap.ext
    intro z
    have hz : z ∈ S.toSubmodule ⊔ T.toSubmodule := by
      rw [hSTsub.codisjoint.eq_top]
      trivial
    obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.mp hz
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hs
    have ht' : t ∈ F ∙ w := by simpa only [hspanT] using ht
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp ht'
    have hcoeffqr : coeff q = coeff r := congrArg Units.val hχ
    simp only [map_add, map_smul, hlift_rep, ← hcoeff_lift, hcoeffqr]
  let R := χ.range
  let _ : Finite R := Finite.of_surjective χ.rangeRestrict χ.rangeRestrict_surjective
  let _ : IsCyclic R := isCyclic_subgroup_units χ.range
  exact isCyclic_of_injective χ.rangeRestrict fun q r hqr =>
    hχinj (congrArg Subtype.val hqr)

variable (p : ℕ) [Fact (Nat.Prime p)]

/-- An algebraic closure `K p` of the finite field `𝔽_p = ZMod p`. -/
noncomputable abbrev K : Type := AlgebraicClosure (ZMod p)

/-- The projective general linear group `PGL₂(K p)`. -/
abbrev PGL : Type := Matrix.ProjGenLinGroup (Fin 2) (K p)

/-- The projective special linear group `PSL₂(K p)`. -/
abbrev PSL : Type := Matrix.ProjectiveSpecialLinearGroup (Fin 2) (K p)

private lemma dickson_stabilizer_isCyclic (G : Subgroup (PGL p)) [Finite G]
    (hG_tame : ¬p ∣ Nat.card G) (x : Projectivization (K p) (Fin 2 → K p)) :
    IsCyclic (MulAction.stabilizer G x) := by
  let S := MulAction.stabilizer G x
  let ι : S →* PGL p := G.subtype.comp S.subtype
  apply dickson_isCyclic_of_fixed_point ι
    (G.subtype_injective.comp S.subtype_injective) x
  · intro g
    exact g.2
  · apply (CharP.cast_eq_zero_iff (K p) p (Nat.card S)).not.mpr
    intro hpS
    apply hG_tame
    exact hpS.trans (Subgroup.card_subgroup_dvd_card S)

private lemma dickson_isCyclic_of_two_exceptional_orbits
    (G : Subgroup (PGL p)) [Finite G] (hG_tame : ¬p ∣ Nat.card G)
    (hG_nontrivial : Nontrivial G)
    (horbits :
      let X := Projectivization (K p) (Fin 2 → K p)
      let E := dicksonExceptional G X
      Nat.card (MulAction.orbitRel.Quotient G E) = 2) : IsCyclic G := by
  let X := Projectivization (K p) (Fin 2 → K p)
  let E := dicksonExceptional G X
  have hfixed (g : G) (hg : g ≠ 1) :
      Nat.card (MulAction.fixedBy X g) = 2 :=
    dickson_card_fixedBy_subgroup p G hG_tame g hg
  let _ : Finite E := dicksonExceptional_finite hfixed
  have hfixedE (g : G) (hg : g ≠ 1) :
      Nat.card (MulAction.fixedBy E g) = 2 := by
    rw [Nat.card_congr (dickson_fixedByExceptionalEquiv g hg)]
    exact hfixed g hg
  have hcount := MulAction.card_add_mul_card_sub_one_eq_card_orbits_mul_card
    G E 2 hfixedE
  have hN : 2 ≤ Nat.card G := by
    have := Finite.one_lt_card (α := G)
    omega
  have hE : Nat.card E = 2 := by
    rw [horbits] at hcount
    omega
  have hquotient_inj : Function.Injective
      (Quotient.mk'' : E → MulAction.orbitRel.Quotient G E) :=
    (Quotient.mk_surjective.bijective_of_nat_card_le (by rw [hE, horbits])).1
  let x : E := Classical.choice (Finite.card_pos_iff.mp (hE ▸ by decide))
  have hfix_all (g : G) : g • x = x := by
    apply hquotient_inj
    exact MulAction.orbitRel.Quotient.quotient_smul_eq
  have hfix_all' (g : G) : g • x.1 = x.1 := congrArg Subtype.val (hfix_all g)
  have hstab : MulAction.stabilizer G x.1 = ⊤ := by
    ext g
    simp only [MulAction.mem_stabilizer_iff, Subgroup.mem_top, iff_true]
    exact hfix_all' g
  have hc := dickson_stabilizer_isCyclic p G hG_tame x.1
  rw [hstab] at hc
  exact Subgroup.topEquiv.isCyclic.mp hc

private lemma dickson_cyclic_or_dihedral_of_orbit_card_two
    (G : Subgroup (PGL p)) [Finite G] (hG_tame : ¬p ∣ Nat.card G)
    (x : dicksonExceptional G (Projectivization (K p) (Fin 2 → K p)))
    (horbit : Nat.card (MulAction.orbit G x) = 2) :
    IsCyclic G ∨
      ∃ n : ℕ, n ≥ 2 ∧ Nonempty (G ≃* DihedralGroup n) := by
  classical
  let X := Projectivization (K p) (Fin 2 → K p)
  let E := dicksonExceptional G X
  let O := MulAction.orbit G x
  let ρ := MulAction.toPermHom G O
  let H := ρ.ker
  have hfixed (g : G) (hg : g ≠ 1) :
      Nat.card (MulAction.fixedBy X g) = 2 :=
    dickson_card_fixedBy_subgroup p G hG_tame g hg
  let _ : Finite E := dicksonExceptional_finite hfixed
  have hfixedE (g : G) (hg : g ≠ 1) :
      Nat.card (MulAction.fixedBy E g) = 2 := by
    rw [Nat.card_congr (dickson_fixedByExceptionalEquiv g hg)]
    exact hfixed g hg
  let _ : Finite O := inferInstance
  have hbase : x ∈ MulAction.orbit G x := ⟨1, one_smul G x⟩
  let xO : O := ⟨x, hbase⟩
  have hOnontrivial : Nontrivial O :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [horbit]; decide)
  obtain ⟨y, hy⟩ := exists_ne xO
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp y.2
  have hρg : ρ g ≠ 1 := by
    intro h
    have heval := Equiv.congr_fun h xO
    apply hy
    apply Subtype.ext
    calc
      y.1 = g • x := hg.symm
      _ = x := congrArg Subtype.val heval
      _ = xO.1 := rfl
  let rg : ρ.range := ⟨ρ g, ⟨g, rfl⟩⟩
  have hrg : rg ≠ 1 := by
    intro h
    apply hρg
    exact congrArg Subtype.val h
  let pair : Fin 2 → ρ.range := ![1, rg]
  have hpair : Function.Injective pair := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [pair]
  have hrange_lower : 2 ≤ Nat.card ρ.range := by
    simpa only [Nat.card_fin] using Nat.card_le_card_of_injective pair hpair
  have hrange_upper : Nat.card ρ.range ≤ 2 := by
    calc
      Nat.card ρ.range ≤ Nat.card (Equiv.Perm O) :=
        Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
      _ = Nat.factorial (Nat.card O) := Nat.card_perm
      _ = 2 := by rw [horbit]; decide
  have hrange : Nat.card ρ.range = 2 := by omega
  have hindex : H.index = 2 := by
    rw [show H = ρ.ker from rfl, Subgroup.index_ker, hrange]
  let S := MulAction.stabilizer G x
  have hHle : H ≤ S := by
    intro k hk
    have hkρ : ρ k = 1 := hk
    have heval := Equiv.congr_fun hkρ xO
    exact congrArg Subtype.val heval
  let _ : IsCyclic S := by
    have hSX : S = MulAction.stabilizer G x.1 := by
      ext k
      simp only [MulAction.mem_stabilizer_iff]
      constructor
      · exact fun h => congrArg Subtype.val h
      · intro h
        change k • x = x
        exact Subtype.ext h
    rw [hSX]
    exact dickson_stabilizer_isCyclic p G hG_tame x.1
  have hHcyc : IsCyclic H := Subgroup.isCyclic_of_le hHle
  have hprodS : Nat.card O * Nat.card S = Nat.card G := by
    let _ := Fintype.ofFinite G
    let _ := Fintype.ofFinite O
    let _ := Fintype.ofFinite S
    simpa only [Nat.card_eq_fintype_card] using
      MulAction.card_orbit_mul_card_stabilizer_eq_card_group (G := G) x
  have hprodH : Nat.card H * 2 = Nat.card G := by
    calc
      Nat.card H * 2 = Nat.card H * H.index := by rw [hindex]
      _ = Nat.card G := H.card_mul_index
  have hHcardS : Nat.card S = Nat.card H := by
    rw [horbit] at hprodS
    omega
  have hHS : H = S := Subgroup.eq_of_le_of_card_ge hHle (by omega)
  have houtside (k : G) (hk : k ∉ H) : k ^ 2 = 1 := by
    have hk1 : k ≠ 1 := by
      intro hk1
      subst k
      exact hk H.one_mem
    let rk : ρ.range := ⟨ρ k, ⟨k, rfl⟩⟩
    have hrkpow : rk ^ 2 = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one]
      have hd := orderOf_dvd_natCard rk
      simpa only [hrange] using hd
    have hρkpow : ρ (k ^ 2) = 1 := by
      have hv := congrArg (fun u : ρ.range => (u : Equiv.Perm O)) hrkpow
      change (ρ k) ^ 2 = 1 at hv
      simpa only [map_pow] using hv
    have hkpowH : k ^ 2 ∈ H := hρkpow
    by_contra hk2
    have hfixk2 : k ^ 2 • x = x := by
      rw [hHS] at hkpowH
      exact hkpowH
    let f : MulAction.fixedBy E k → MulAction.fixedBy E (k ^ 2) := fun z =>
      ⟨z.1, by
        rw [MulAction.mem_fixedBy]
        rw [pow_two, mul_smul]
        have hzfix := MulAction.mem_fixedBy.mp z.2
        rw [hzfix, hzfix]⟩
    have hfinj : Function.Injective f := by
      intro z w hzw
      apply Subtype.ext
      exact congrArg (fun u : MulAction.fixedBy E (k ^ 2) => u.1) hzw
    let _ : Finite (MulAction.fixedBy E k) :=
      Nat.finite_of_card_ne_zero (by rw [hfixedE k hk1]; decide)
    let _ : Finite (MulAction.fixedBy E (k ^ 2)) :=
      Nat.finite_of_card_ne_zero (by rw [hfixedE (k ^ 2) hk2]; decide)
    have hfbij : Function.Bijective f := hfinj.bijective_of_nat_card_le (by
      rw [hfixedE k hk1, hfixedE (k ^ 2) hk2])
    obtain ⟨z, hz⟩ := hfbij.2 ⟨x, hfixk2⟩
    apply hk
    rw [hHS]
    have hzx : z.1 = x := congrArg (fun u : MulAction.fixedBy E (k ^ 2) => u.1) hz
    change k • x = x
    have hzfix := MulAction.mem_fixedBy.mp z.2
    simpa only [hzx] using hzfix
  by_cases hH1 : Nat.card H = 1
  · left
    have hG2 : Nat.card G = 2 := by omega
    let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact isCyclic_of_prime_card hG2
  · right
    have hH2 : 2 ≤ Nat.card H := by
      have hHpos : 0 < Nat.card H := Nat.card_pos
      omega
    exact ⟨Nat.card H, hH2, dickson_dihedral_of_index_two H hHcyc hindex houtside hH2⟩

private lemma dickson_cyclic_or_dihedral_of_normal_cyclic_subgroup
    (G : Subgroup (PGL p)) [Finite G] (hG_tame : ¬p ∣ Nat.card G)
    (H : Subgroup G) [H.Normal] [Nontrivial H] (hHcyc : IsCyclic H) :
    IsCyclic G ∨
      ∃ n : ℕ, n ≥ 2 ∧ Nonempty (G ≃* DihedralGroup n) := by
  classical
  let X := Projectivization (K p) (Fin 2 → K p)
  let E := dicksonExceptional G X
  let _ : IsCyclic H := hHcyc
  obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := H)
  have hu1 : (u : G) ≠ 1 := by
    intro hu1
    obtain ⟨v, hv⟩ := exists_ne (1 : H)
    apply hv
    have hvpow := hu v
    have huH : u = (1 : H) := Subtype.ext hu1
    rw [huH] at hvpow
    have : (1 : H) = v := by
      simpa only [Subgroup.mem_zpowers_iff, one_zpow, exists_const] using hvpow
    exact this.symm
  let g : G := u
  let F := MulAction.fixedBy X g
  have hF : Nat.card F = 2 := dickson_card_fixedBy_subgroup p G hG_tame g hu1
  have hFdata : Nonempty F ∧ Finite F := Nat.card_pos_iff.mp (by rw [hF]; decide)
  let _ : Finite F := hFdata.2
  let xF : F := Classical.choice hFdata.1
  have hufix : u • xF.1 = xF.1 := MulAction.mem_fixedBy.mp xF.2
  have hHfix (v : H) : (v : G) • xF.1 = xF.1 := by
    exact smul_eq_self_of_mem_zpowers (hu v) hufix
  let xE : E := ⟨xF.1, ⟨g, hu1, MulAction.mem_fixedBy.mp xF.2⟩⟩
  have hfixed (a : G) (ha : a ≠ 1) : Nat.card (MulAction.fixedBy X a) = 2 :=
    dickson_card_fixedBy_subgroup p G hG_tame a ha
  let _ : Finite E := dicksonExceptional_finite hfixed
  have htranslate (a : G) : g • (a • xF.1) = a • xF.1 := by
    let c : H := ⟨a⁻¹ * g * a, (inferInstance : H.Normal).conj_mem' g u.2 a⟩
    calc
      g • (a • xF.1) = (g * a) • xF.1 := (mul_smul g a xF.1).symm
      _ = (a * (a⁻¹ * g * a)) • xF.1 := by congr 1; group
      _ = a • ((c : G) • xF.1) := mul_smul a (c : G) xF.1
      _ = a • xF.1 := by rw [hHfix c]
  have horbit_fixed (y : E) (hy : y ∈ MulAction.orbit G xE) : g • y.1 = y.1 := by
    obtain ⟨a, ha⟩ := hy
    have hay : a • xE.1 = y.1 := congrArg Subtype.val ha
    rw [← hay]
    exact htranslate a
  let O := MulAction.orbit G xE
  let f : O → F := fun y => ⟨y.1.1, MulAction.mem_fixedBy.mpr (horbit_fixed y.1 y.2)⟩
  have hfinj : Function.Injective f := by
    intro y z hyz
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun w : F => w.1) hyz
  have hOupper : Nat.card O ≤ 2 := by
    rw [← hF]
    exact Nat.card_le_card_of_injective f hfinj
  let xO : O := ⟨xE, MulAction.mem_orbit_iff.mpr ⟨1, one_smul G xE⟩⟩
  let _ : Nonempty O := ⟨xO⟩
  have hOpos : 0 < Nat.card O := Nat.card_pos
  have hO : Nat.card O = 1 ∨ Nat.card O = 2 := by omega
  rcases hO with hO | hO
  · left
    have hOsub : Subsingleton O := (Nat.card_eq_one_iff_unique.mp hO).1
    have hfix_all (a : G) : a • xE = xE := by
      let ya : O := ⟨a • xE, MulAction.mem_orbit_iff.mpr ⟨a, rfl⟩⟩
      have h := congrArg (fun y : O => y.1) (hOsub.elim ya xO)
      exact h
    have hstab : MulAction.stabilizer G xE.1 = ⊤ := by
      ext a
      simp only [MulAction.mem_stabilizer_iff, Subgroup.mem_top, iff_true]
      exact congrArg Subtype.val (hfix_all a)
    have hc := dickson_stabilizer_isCyclic p G hG_tame xE.1
    rw [hstab] at hc
    exact Subgroup.topEquiv.isCyclic.mp hc
  · exact dickson_cyclic_or_dihedral_of_orbit_card_two p G hG_tame xE hO

private lemma dickson_order_twenty_four
    (G : Subgroup (PGL p)) [Finite G] (hG_tame : ¬p ∣ Nat.card G)
    (hG24 : Nat.card G = 24) :
    IsCyclic G ∨
      (∃ n : ℕ, n ≥ 2 ∧ Nonempty (G ≃* DihedralGroup n)) ∨
      Nonempty (G ≃* Equiv.Perm (Fin 4)) := by
  classical
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  let P : Sylow 3 G := Classical.choice inferInstance
  have hP3 : Nat.card P = 3 := by
    rw [Sylow.card_eq_multiplicity, hG24]
    norm_num [Nat.factorization]
  have hPindex : P.index = 8 := by
    rw [Subgroup.index_eq_card_div, hG24, hP3]
  have hn3dvd : Nat.card (Sylow 3 G) ∣ 8 := by
    rw [← hPindex]
    exact P.card_dvd_index
  have hn3mod := card_sylow_modEq_one 3 G
  have hn3le : Nat.card (Sylow 3 G) ≤ 8 := Nat.le_of_dvd (by decide) hn3dvd
  have hn3 : Nat.card (Sylow 3 G) = 1 ∨ Nat.card (Sylow 3 G) = 4 := by
    interval_cases Nat.card (Sylow 3 G) <;> simp_all [Nat.ModEq]
  rcases hn3 with hn3 | hn3
  · let _ : Subsingleton (Sylow 3 G) := (Nat.card_eq_one_iff_unique.mp hn3).1
    let _ : P.Normal := Sylow.normal_of_subsingleton P
    let _ : Nontrivial P := Finite.one_lt_card_iff_nontrivial.mp (by rw [hP3]; decide)
    have h := dickson_cyclic_or_dihedral_of_normal_cyclic_subgroup p G hG_tame P
      (isCyclic_of_prime_card hP3)
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · let ρ := MulAction.toPermHom G (Sylow 3 G)
    let H := ρ.ker
    have hnot3H : ¬3 ∣ Nat.card H := by
      intro h3H
      obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := H) 3 h3H
      let g : G := u
      have hgorder : orderOf g = 3 := by simpa [g] using (Subgroup.orderOf_coe u).trans hu
      let R : Subgroup G := Subgroup.zpowers g
      have hRcard : Nat.card R = 3 := by
        rw [show Nat.card R = orderOf g by exact Nat.card_zpowers g, hgorder]
      have hfactor : 3 ^ (Nat.card G).factorization 3 = 3 := by
        rw [hG24]
        norm_num [Nat.factorization]
      let Q₀ : Sylow 3 G := Sylow.ofCard R (hRcard.trans hfactor.symm)
      have hgker : g ∈ H := u.2
      have hQ₀norm (Q : Sylow 3 G) : (Q₀ : Subgroup G) ≤ Subgroup.normalizer Q := by
        have hρg : ρ g = 1 := hgker
        have hgfix : g • Q = Q := by
          exact Equiv.congr_fun hρg Q
        have hgnorm : g ∈ Subgroup.normalizer Q := Sylow.smul_eq_iff_mem_normalizer.mp hgfix
        simpa [Q₀, R] using (Subgroup.zpowers_le.mpr hgnorm)
      have hall (Q : Sylow 3 G) : Q = Q₀ := by
        have hQ₀Q : (Q₀ : Subgroup G) ≤ Q := by
          rw [← inf_eq_left, ← Q₀.isPGroup'.inf_normalizer_sylow Q]
          exact inf_eq_left.mpr (hQ₀norm Q)
        exact Sylow.ext (Q₀.is_maximal' Q.isPGroup' hQ₀Q)
      have hsub : Subsingleton (Sylow 3 G) := ⟨fun Q _ => (hall Q).trans (hall _).symm⟩
      have hone := (Nat.card_eq_one_iff_unique.mpr ⟨hsub, inferInstance⟩)
      omega
    have hHle : H ≤ MulAction.stabilizer G P := by
      intro g hg
      have hρg : ρ g = 1 := hg
      exact Equiv.congr_fun hρg P
    have hstabindex : (MulAction.stabilizer G P).index = 4 := by
      rw [P.stabilizer_eq_normalizer, ← P.card_eq_index_normalizer, hn3]
    have hindex4 : 4 ∣ H.index := by
      rw [← hstabindex]
      exact Subgroup.index_dvd_of_le hHle
    have hprod : Nat.card H * H.index = 24 := by rw [H.card_mul_index, hG24]
    have hindex0 : H.index ≠ 0 := by intro h; simp_all
    have hindexge : 4 ≤ H.index :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero hindex0) hindex4
    have hHle6 : Nat.card H ≤ 6 := by nlinarith
    have hHcard : Nat.card H = 1 ∨ Nat.card H = 2 := by
      have hHpos : 0 < Nat.card H := Nat.card_pos
      interval_cases Nat.card H <;> simp_all [Nat.dvd_iff_mod_eq_zero] <;> omega
    rcases hHcard with hHcard | hHcard
    · right; right
      have hρinj : Function.Injective ρ :=
        (ρ.ker_eq_bot_iff).mp (Subgroup.card_eq_one.mp hHcard)
      let _ := Fintype.ofFinite (Sylow 3 G)
      have hSylowFintype : Fintype.card (Sylow 3 G) = 4 := by
        simpa only [Nat.card_eq_fintype_card] using hn3
      let q : Sylow 3 G ≃ Fin 4 := Fintype.equivFinOfCardEq hSylowFintype
      let σ : G →* Equiv.Perm (Fin 4) := q.permCongrHom.toMonoidHom.comp ρ
      have hσinj : Function.Injective σ := q.permCongrHom.injective.comp hρinj
      have hcardle : Nat.card (Equiv.Perm (Fin 4)) ≤ Nat.card G := by
        rw [Nat.card_perm, Nat.card_fin, hG24]
        norm_num [Nat.factorial]
      exact ⟨MulEquiv.ofBijective σ (hσinj.bijective_of_nat_card_le hcardle)⟩
    · let _ : Nontrivial H :=
        Finite.one_lt_card_iff_nontrivial.mp (by rw [hHcard]; decide)
      have h := dickson_cyclic_or_dihedral_of_normal_cyclic_subgroup p G hG_tame H
        (isCyclic_of_prime_card hHcard)
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)

private lemma dickson_order_sixty
    (G : Subgroup (PGL p)) [Finite G] (hG_tame : ¬p ∣ Nat.card G)
    (hG60 : Nat.card G = 60)
    (horbits : Nat.card (MulAction.orbitRel.Quotient G
      (dicksonExceptional G (Projectivization (K p) (Fin 2 → K p)))) = 3)
    (x₂ x₃ x₅ : dicksonExceptional G (Projectivization (K p) (Fin 2 → K p)))
    (h₂ : Nat.card (MulAction.stabilizer G x₂) = 2)
    (h₃ : Nat.card (MulAction.stabilizer G x₃) = 3)
    (h₅ : Nat.card (MulAction.stabilizer G x₅) = 5)
    (hall : ∀ x : dicksonExceptional G (Projectivization (K p) (Fin 2 → K p)),
      Nat.card (MulAction.stabilizer G x) = 2 ∨
      Nat.card (MulAction.stabilizer G x) = 3 ∨
      Nat.card (MulAction.stabilizer G x) = 5) :
    IsCyclic G ∨
      (∃ n : ℕ, n ≥ 2 ∧ Nonempty (G ≃* DihedralGroup n)) ∨
      Nonempty (G ≃* alternatingGroup (Fin 5)) := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hn₂ : Nat.card (Sylow 2 G) = 5 :=
    dickson_card_sylow_two_eq_five p G hG_tame hG60 horbits
      x₂ x₃ x₅ h₂ h₃ h₅ hall
  let P : Sylow 2 G := Classical.choice inferInstance
  let ρ := MulAction.toPermHom G (Sylow 2 G)
  let H := ρ.ker
  have hnot2H : ¬2 ∣ Nat.card H := by
    intro h2H
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := H) 2 h2H
    let g : G := u
    have hgorder : orderOf g = 2 := by
      exact (Subgroup.orderOf_coe u).trans hu
    let R : Subgroup G := Subgroup.zpowers g
    have hRcard : Nat.card R = 2 := by
      rw [show Nat.card R = orderOf g by exact Nat.card_zpowers g, hgorder]
    have hRgroup : IsPGroup 2 R := IsPGroup.of_card (hRcard.trans (pow_one 2).symm)
    have hgker : g ∈ H := u.2
    have hgmem (Q : Sylow 2 G) : g ∈ Q := by
      have hρg : ρ g = 1 := hgker
      have hgfix : g • Q = Q := Equiv.congr_fun hρg Q
      have hRnorm : R ≤ Subgroup.normalizer Q := by
        apply Subgroup.zpowers_le.mpr
        exact Sylow.smul_eq_iff_mem_normalizer.mp hgfix
      have hRQ : R ≤ Q := by
        rw [← inf_eq_left, ← hRgroup.inf_normalizer_sylow Q]
        exact inf_eq_left.mpr hRnorm
      exact hRQ (Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩)
    let _ : Nontrivial (Sylow 2 G) :=
      Finite.one_lt_card_iff_nontrivial.mp (by rw [hn₂]; decide)
    obtain ⟨Q, hQP⟩ := exists_ne P
    have heq := dickson_sylow_two_unique_of_mem p G hG_tame hG60 hall
      g hgorder P Q (hgmem P) (hgmem Q)
    exact hQP heq.symm
  have hHle : H ≤ MulAction.stabilizer G P := by
    intro g hg
    have hρg : ρ g = 1 := hg
    exact Equiv.congr_fun hρg P
  have hstabindex : (MulAction.stabilizer G P).index = 5 := by
    rw [P.stabilizer_eq_normalizer, ← P.card_eq_index_normalizer, hn₂]
  have hindex5 : 5 ∣ H.index := by
    rw [← hstabindex]
    exact Subgroup.index_dvd_of_le hHle
  have hprod : Nat.card H * H.index = 60 := by rw [H.card_mul_index, hG60]
  have hindex0 : H.index ≠ 0 := by intro h; simp_all
  have hindexge : 5 ≤ H.index :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hindex0) hindex5
  have hHle12 : Nat.card H ≤ 12 := by nlinarith
  have hHcard : Nat.card H = 1 ∨ Nat.card H = 3 := by
    have hHpos : 0 < Nat.card H := Nat.card_pos
    interval_cases Nat.card H <;> simp_all [Nat.dvd_iff_mod_eq_zero] <;> omega
  rcases hHcard with hHcard | hHcard
  · right; right
    have hρinj : Function.Injective ρ :=
      (ρ.ker_eq_bot_iff).mp (Subgroup.card_eq_one.mp hHcard)
    let _ := Fintype.ofFinite (Sylow 2 G)
    have hSylowFintype : Fintype.card (Sylow 2 G) = 5 := by
      simpa only [Nat.card_eq_fintype_card] using hn₂
    let q : Sylow 2 G ≃ Fin 5 := Fintype.equivFinOfCardEq hSylowFintype
    let σ : G →* Equiv.Perm (Fin 5) := q.permCongrHom.toMonoidHom.comp ρ
    have hσinj : Function.Injective σ := q.permCongrHom.injective.comp hρinj
    have hrange_card : Nat.card σ.range = 60 := by
      calc
        Nat.card σ.range = Nat.card G := (Nat.card_congr (MonoidHom.ofInjective hσinj)).symm
        _ = 60 := hG60
    have hindex : σ.range.index = 2 := by
      rw [Subgroup.index_eq_card_div, Nat.card_perm, Nat.card_fin, hrange_card]
      norm_num [Nat.factorial]
    have hrange : σ.range = alternatingGroup (Fin 5) :=
      Equiv.Perm.eq_alternatingGroup_of_index_eq_two hindex
    let eG : G ≃* σ.range := MonoidHom.ofInjective hσinj
    rw [hrange] at eG
    exact ⟨eG⟩
  · let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
    let _ : Nontrivial H :=
      Finite.one_lt_card_iff_nontrivial.mp (by rw [hHcard]; decide)
    have h := dickson_cyclic_or_dihedral_of_normal_cyclic_subgroup p G hG_tame H
      (isCyclic_of_prime_card hHcard)
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

variable [Fact (2 < p)]

/-- **Dickson's classification**, tame case: a finite nontrivial subgroup of
`PGL₂` over an algebraic closure of `𝔽_p` (odd `p`), of order prime to `p`, is
cyclic, dihedral, or one of `A₄`, `S₄`, `A₅`.

Source: L. E. Dickson, *Linear Groups with an Exposition of the Galois Field
Theory*, Teubner (1901).

Proves `Wanted` entry `classification_tame`.

Proof: Klein's orbit count on the projective line, followed by identification
of the resulting orbit signatures.
-/
theorem classification_tame (G : Subgroup (PGL p)) [Finite G]
    (hG_tame : ¬ (p : ℕ) ∣ Nat.card G)
    (hG_nontrivial : Nontrivial G) :
    (IsCyclic G) ∨
    (∃ n : ℕ, n ≥ 2 ∧ Nonempty (G ≃* DihedralGroup n)) ∨
    (Nonempty (G ≃* alternatingGroup (Fin 4))) ∨
    (Nonempty (G ≃* Equiv.Perm (Fin 4))) ∨
    (Nonempty (G ≃* alternatingGroup (Fin 5))) := by
  classical
  let X := Projectivization (K p) (Fin 2 → K p)
  let E := dicksonExceptional G X
  rcases dickson_card_orbits_exceptional p G hG_tame hG_nontrivial with horbits | horbits
  · exact Or.inl (dickson_isCyclic_of_two_exceptional_orbits p G hG_tame
      hG_nontrivial horbits)
  · rcases dickson_exceptional_signature p G hG_tame hG_nontrivial horbits with
      ⟨n, hn, hGn, ⟨x, hstab⟩, _hall⟩ |
      ⟨hG12, ⟨x, hstab⟩, _hall⟩ |
      ⟨hG24, _x₃, _x₄, _hall⟩ |
      ⟨hG60, ⟨x₂, hx₂⟩, ⟨x₃, hx₃⟩, ⟨x₅, hx₅⟩, hall⟩
    · let O := MulAction.orbit G x
      let orbitMap : G → O := fun g => ⟨g • x, MulAction.mem_orbit_iff.mpr ⟨g, rfl⟩⟩
      have horbitMap : Function.Surjective orbitMap := by
        intro y
        obtain ⟨g, hg⟩ := y.2
        exact ⟨g, Subtype.ext hg⟩
      let _ : Finite O := Finite.of_surjective orbitMap horbitMap
      let _ := Fintype.ofFinite G
      let _ := Fintype.ofFinite O
      let _ := Fintype.ofFinite (MulAction.stabilizer G x)
      have hprod : Nat.card O * Nat.card (MulAction.stabilizer G x) = Nat.card G := by
        simpa only [Nat.card_eq_fintype_card] using
          MulAction.card_orbit_mul_card_stabilizer_eq_card_group (G := G) x
      have hO : Nat.card O = 2 := by
        rw [hstab, hGn] at hprod
        nlinarith
      rcases dickson_cyclic_or_dihedral_of_orbit_card_two p G hG_tame x hO with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl
        (dickson_isAlternatingFour p G hG_tame hG12 x hstab)))
    · rcases dickson_order_twenty_four p G hG_tame hG24 with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · rcases dickson_order_sixty p G hG_tame hG60 horbits
        x₂ x₃ x₅ hx₂ hx₃ hx₅ hall with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

end Dickson

end MetaMathlibExt
