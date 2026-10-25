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
import Def.GroupTheory.DicksonPGL2Tame.Part4
/-!
# Tame finite subgroups of `PGL₂`

This file classifies finite subgroups of `PGL₂` whose order is prime to the
characteristic, using the action on the projective line.
-/


namespace MetaMathlibExt

open scoped BigOperators

namespace Dickson

lemma dickson_normalizedLift_mk {F : Type*} [Field F]
    (x : Projectivization F (Fin 2 → F))
    (h : MulAction.stabilizer (Matrix.ProjGenLinGroup (Fin 2) F) x) :
    Matrix.ProjGenLinGroup.mk (dickson_normalizedLift x h) = h.1 :=
  dickson_normalizedLiftFun_mk x h

lemma dickson_normalizedLift_rep {F : Type*} [Field F]
    (x : Projectivization F (Fin 2 → F))
    (h : MulAction.stabilizer (Matrix.ProjGenLinGroup (Fin 2) F) x) :
    (↑(Matrix.GeneralLinearGroup.toLin (dickson_normalizedLift x h)) :
      Module.End F (Fin 2 → F)) x.rep = x.rep :=
  dickson_normalizedLiftFun_rep x h

lemma dickson_isCyclic_of_fixed_point {F Q : Type*} [Field F]
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

end Dickson
end MetaMathlibExt
