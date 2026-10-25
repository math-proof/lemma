/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/DicksonPGL2Wild.lean -/

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
import Theorem.GroupTheory.DicksonPGL2Tame.Part4
import Lemma.Nat.Card_Stabilizer
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.Algebra.Group.IsCommutative
import Mathlib.Algebra.Module.ZMod
import Mathlib.FieldTheory.Separable
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.SchurZassenhaus
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import Def.GroupTheory.DicksonPGL2Wild.Part8
/-!
# Dickson's classification in the wild case

This file classifies finite subgroups of `PGL₂` over an algebraic closure of an odd finite
field when the characteristic divides the group order. It also supplies the projective linear
group order formulas and characteristic-order element facts used by the classification.
-/


namespace MetaMathlibExt

namespace Dickson

open scoped BigOperators Pointwise Polynomial

lemma dicksonWild_card_order_char_with_multiplier_eq_two
    {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
    (G : Subgroup (PGL p)) [Finite G] (hpG : p ∣ Nat.card G) (P : Sylow p G)
    (m f t : ℕ) (htp : Nat.Coprime t p)
    (hPcard : Nat.card (P : Subgroup G) = p ^ m)
    (hNcard : Nat.card (Subgroup.normalizer (P : Set G)) = p ^ m * t)
    (hindex : (Subgroup.normalizer (P : Set G)).index = 1 + f * p ^ m)
    (hcount : Nat.card {g : G // g ≠ 1 ∧ g ^ p = 1} =
      (1 + f * p ^ m) * (p ^ m - 1))
    (hhalf : 2 * t = p ^ m - 1)
    (M : Subfield (K p)) [Finite M] (L : Subgroup Mˣ)
    (hLcard : Nat.card L = t) (j : G →* PGL p) (hj : Function.Injective j)
    (coord : Subgroup.normalizer (P : Set G) → M × L)
    (hcoord : Function.Bijective coord)
    (hnormal : ∀ n : Subgroup.normalizer (P : Set G),
      j n.1 = Matrix.ProjGenLinGroup.map M.subtype
        (Matrix.ProjGenLinGroup.mk
          (DicksonWildAffine.affineGL (coord n).1 (coord n).2.1)))
    (hout : ∀ g : G, g ∉ Subgroup.normalizer (P : Set G) →
      ∃ S : GL (Fin 2) (K p), Matrix.ProjGenLinGroup.mk S = j g ∧
        (S : Matrix (Fin 2) (Fin 2) (K p)) 1 0 ≠ 0)
    (g : G) (hg : g ∉ Subgroup.normalizer (P : Set G)) (l : L) :
    Nat.card {n : {n : Subgroup.normalizer (P : Set G) //
      (g * (n.1 : G)) ^ p = 1} // (coord n.1).2 = l} = 2 := by
  classical
  let N := Subgroup.normalizer (P : Set G)
  let E := {n : N // (g * (n.1 : G)) ^ p = 1}
  let toL : E → L := fun n ↦ (coord n.1).2
  let A : N → GL (Fin 2) (K p) := fun n ↦
    Matrix.GeneralLinearGroup.map M.subtype
      (DicksonWildAffine.affineGL (coord n).1 (coord n).2.1)
  have hA (n : N) : A n = DicksonWildAffine.affineGL ((coord n).1 : K p)
      (Units.map M.subtype.toMonoidHom (coord n).2.1) :=
    DicksonWildAffine.affineGL_map_subfield M (coord n).1 (coord n).2.1
  have hnormal' (n : N) : j n.1 = Matrix.ProjGenLinGroup.mk (A n) := by
    rw [hnormal n, Matrix.ProjGenLinGroup.map_mk]
  obtain ⟨S, hS, hS10⟩ := hout g hg
  have hEcard : Nat.card E = 2 * t :=
    dicksonWild_card_order_char_in_normalizer_coset_eq G hpG P m f t htp
      hPcard hNcard hindex hcount hhalf g hg
  have hfiber (u : L) : Nat.card {n : E // toL n = u} ≤ 2 := by
    let uK : (K p)ˣ := Units.map M.subtype.toMonoidHom u.1
    let c : K p := 4 * Matrix.det (S : Matrix (Fin 2) (Fin 2) (K p)) * (uK : K p)
    let toRoot : {n : E // toL n = u} → {x : K p // x ^ 2 = c} := fun n ↦ ⟨
      Matrix.trace (((S * A n.1.1 : GL (Fin 2) (K p)) :
        Matrix (Fin 2) (Fin 2) (K p))), by
        have hnSecond : (coord n.1.1).2 = u := n.2
        have hgne : g * (n.1.1.1 : G) ≠ 1 := by
          intro hone
          apply hg
          have hgeq : g = (n.1.1.1 : G)⁻¹ := eq_inv_of_mul_eq_one_left hone
          rw [hgeq]
          exact N.inv_mem n.1.1.2
        have horderG : orderOf (g * (n.1.1.1 : G)) = p :=
          orderOf_eq_prime n.1.2 hgne
        have horderJ : orderOf (j (g * (n.1.1.1 : G))) = p :=
          (orderOf_injective j hj (g * (n.1.1.1 : G))).trans horderG
        have hmk : Matrix.ProjGenLinGroup.mk (S * A n.1.1) =
            j (g * (n.1.1.1 : G)) := by
          calc
            Matrix.ProjGenLinGroup.mk (S * A n.1.1) =
                Matrix.ProjGenLinGroup.mk S * Matrix.ProjGenLinGroup.mk (A n.1.1) :=
              map_mul Matrix.ProjGenLinGroup.mk S (A n.1.1)
            _ = j g * j n.1.1.1 := by rw [hS, hnormal' n.1.1]
            _ = j (g * (n.1.1.1 : G)) := (map_mul j g n.1.1.1).symm
        have hpar : ((S * A n.1.1 : GL (Fin 2) (K p)) :
            Matrix (Fin 2) (Fin 2) (K p)).IsParabolic := by
          apply dicksonWild_lift_isParabolic_of_order_eq_char
          rw [hmk]
          exact horderJ
        have hdisc := hpar.2
        rw [Matrix.discr_fin_two] at hdisc
        have heq := sub_eq_zero.mp hdisc
        rw [hA n.1.1, hnSecond, DicksonWildAffine.det_mul_affineGL] at heq
        rw [hA n.1.1, hnSecond]
        simpa [c, uK, mul_assoc] using heq⟩
    have htoRoot : Function.Injective toRoot := by
      intro x y hxy
      have hxSecond : (coord x.1.1).2 = u := x.2
      have hySecond : (coord y.1.1).2 = u := y.2
      have htrace := congrArg (fun z : {w : K p // w ^ 2 = c} ↦ z.1) hxy
      change Matrix.trace (((S * A x.1.1 : GL (Fin 2) (K p)) :
          Matrix (Fin 2) (Fin 2) (K p))) =
        Matrix.trace (((S * A y.1.1 : GL (Fin 2) (K p)) :
          Matrix (Fin 2) (Fin 2) (K p))) at htrace
      rw [hA x.1.1, hA y.1.1, hxSecond, hySecond,
        DicksonWildAffine.trace_mul_affineGL,
        DicksonWildAffine.trace_mul_affineGL] at htrace
      have hfirst : (coord x.1.1).1 = (coord y.1.1).1 := by
        apply Subtype.ext
        apply mul_left_cancel₀ hS10
        linear_combination htrace
      have hcoordEq : coord x.1.1 = coord y.1.1 := by
        apply Prod.ext hfirst
        exact hxSecond.trans hySecond.symm
      have hn : x.1.1 = y.1.1 := hcoord.1 hcoordEq
      apply Subtype.ext
      apply Subtype.ext
      exact hn
    let q : (K p)[X] := Polynomial.X ^ 2 - Polynomial.C c
    have hq0 : q ≠ 0 := Polynomial.X_pow_sub_C_ne_zero (by decide) c
    have hfinite : Set.Finite {x : K p | x ^ 2 = c} := by
      apply (Finset.finite_toSet (q.map (algebraMap (K p) (K p))).roots.toFinset).subset
      intro x hx
      rw [show (q.map (algebraMap (K p) (K p))).roots.toFinset = q.rootSet (K p) by rfl,
        Polynomial.mem_rootSet_of_ne hq0]
      change x ^ 2 = c at hx
      simpa [q] using sub_eq_zero.mpr hx
    let _ : Fintype {x : K p // x ^ 2 = c} := hfinite.fintype
    exact (Nat.card_le_card_of_injective toRoot htoRoot).trans
      (DicksonWildAffine.card_quadraticFiber_le_two c)
  have htotal : Nat.card E = 2 * Nat.card L := by rw [hEcard, hLcard]
  have hfiberEq : ∀ u : L, Nat.card {n : E // toL n = u} = 2 :=
    DicksonWildAffine.card_fiber_eq_of_le_of_card_eq_mul toL 2 hfiber htotal
  exact hfiberEq l

set_option maxHeartbeats 800000 in
-- The trace-fiber argument expands several nested finite subtypes.
lemma dicksonWild_exists_order_char_with_multiplier_and_trace
    {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
    (G : Subgroup (PGL p)) [Finite G] (hpG : p ∣ Nat.card G) (P : Sylow p G)
    (m f t : ℕ) (htp : Nat.Coprime t p)
    (hPcard : Nat.card (P : Subgroup G) = p ^ m)
    (hNcard : Nat.card (Subgroup.normalizer (P : Set G)) = p ^ m * t)
    (hindex : (Subgroup.normalizer (P : Set G)).index = 1 + f * p ^ m)
    (hcount : Nat.card {g : G // g ≠ 1 ∧ g ^ p = 1} =
      (1 + f * p ^ m) * (p ^ m - 1))
    (hhalf : 2 * t = p ^ m - 1)
    (M : Subfield (K p)) [Finite M] (L : Subgroup Mˣ)
    (hLcard : Nat.card L = t) (j : G →* PGL p) (hj : Function.Injective j)
    (coord : Subgroup.normalizer (P : Set G) → M × L)
    (hcoord : Function.Bijective coord)
    (hnormal : ∀ n : Subgroup.normalizer (P : Set G),
      j n.1 = Matrix.ProjGenLinGroup.map M.subtype
        (Matrix.ProjGenLinGroup.mk
          (DicksonWildAffine.affineGL (coord n).1 (coord n).2.1)))
    (hout : ∀ g : G, g ∉ Subgroup.normalizer (P : Set G) →
      ∃ S : GL (Fin 2) (K p), Matrix.ProjGenLinGroup.mk S = j g ∧
        (S : Matrix (Fin 2) (Fin 2) (K p)) 1 0 ≠ 0)
    (g : G) (hg : g ∉ Subgroup.normalizer (P : Set G))
    (S : GL (Fin 2) (K p)) (hS : Matrix.ProjGenLinGroup.mk S = j g)
    (hS10 : (S : Matrix (Fin 2) (Fin 2) (K p)) 1 0 ≠ 0)
    (l : L) (r : K p)
    (hr : r ^ 2 = 4 * Matrix.det (S : Matrix (Fin 2) (Fin 2) (K p)) *
      (Units.map M.subtype.toMonoidHom l.1 : K p)) :
    ∃ n : Subgroup.normalizer (P : Set G),
      (g * (n.1 : G)) ^ p = 1 ∧ (coord n).2 = l ∧
      Matrix.trace (((S * Matrix.GeneralLinearGroup.map M.subtype
        (DicksonWildAffine.affineGL (coord n).1 (coord n).2.1) :
          GL (Fin 2) (K p)) : Matrix (Fin 2) (Fin 2) (K p))) = r := by
  classical
  let N := Subgroup.normalizer (P : Set G)
  let X := {n : {n : N // (g * (n.1 : G)) ^ p = 1} // (coord n.1).2 = l}
  have hXcard : Nat.card X = 2 :=
    dicksonWild_card_order_char_with_multiplier_eq_two G hpG P m f t htp
      hPcard hNcard hindex hcount hhalf M L hLcard j hj coord hcoord hnormal hout g hg l
  obtain ⟨x, y, hxy, -⟩ := Nat.card_eq_two_iff.mp hXcard
  let A : N → GL (Fin 2) (K p) := fun n ↦
    Matrix.GeneralLinearGroup.map M.subtype
      (DicksonWildAffine.affineGL (coord n).1 (coord n).2.1)
  have hA (n : N) : A n = DicksonWildAffine.affineGL ((coord n).1 : K p)
      (Units.map M.subtype.toMonoidHom (coord n).2.1) :=
    DicksonWildAffine.affineGL_map_subfield M (coord n).1 (coord n).2.1
  have hnormal' (n : N) : j n.1 = Matrix.ProjGenLinGroup.mk (A n) := by
    rw [hnormal n, Matrix.ProjGenLinGroup.map_mk]
  have htraceSq (z : X) :
      Matrix.trace (((S * A z.1.1 : GL (Fin 2) (K p)) :
        Matrix (Fin 2) (Fin 2) (K p))) ^ 2 = r ^ 2 := by
    have hgne : g * (z.1.1.1 : G) ≠ 1 := by
      intro hone
      apply hg
      have hgeq : g = (z.1.1.1 : G)⁻¹ := eq_inv_of_mul_eq_one_left hone
      rw [hgeq]
      exact N.inv_mem z.1.1.2
    have horderG : orderOf (g * (z.1.1.1 : G)) = p :=
      orderOf_eq_prime z.1.2 hgne
    have horderJ : orderOf (j (g * (z.1.1.1 : G))) = p :=
      (orderOf_injective j hj (g * (z.1.1.1 : G))).trans horderG
    have hmk : Matrix.ProjGenLinGroup.mk (S * A z.1.1) =
        j (g * (z.1.1.1 : G)) := by
      calc
        Matrix.ProjGenLinGroup.mk (S * A z.1.1) =
            Matrix.ProjGenLinGroup.mk S * Matrix.ProjGenLinGroup.mk (A z.1.1) :=
          map_mul Matrix.ProjGenLinGroup.mk S (A z.1.1)
        _ = j g * j z.1.1.1 := by rw [hS, hnormal' z.1.1]
        _ = j (g * (z.1.1.1 : G)) := (map_mul j g z.1.1.1).symm
    have hpar : ((S * A z.1.1 : GL (Fin 2) (K p)) :
        Matrix (Fin 2) (Fin 2) (K p)).IsParabolic := by
      apply dicksonWild_lift_isParabolic_of_order_eq_char
      rw [hmk]
      exact horderJ
    have hdisc := hpar.2
    rw [Matrix.discr_fin_two] at hdisc
    have heq := sub_eq_zero.mp hdisc
    have hdet : Matrix.det (((S * A z.1.1 : GL (Fin 2) (K p)) :
        Matrix (Fin 2) (Fin 2) (K p))) =
        Matrix.det (S : Matrix (Fin 2) (Fin 2) (K p)) *
          (Units.map M.subtype.toMonoidHom l.1 : K p) := by
      rw [hA z.1.1, z.2, DicksonWildAffine.det_mul_affineGL]
    rw [hdet] at heq
    calc
      Matrix.trace (((S * A z.1.1 : GL (Fin 2) (K p)) :
          Matrix (Fin 2) (Fin 2) (K p))) ^ 2 =
          4 * (Matrix.det (S : Matrix (Fin 2) (Fin 2) (K p)) *
            (Units.map M.subtype.toMonoidHom l.1 : K p)) := heq
      _ = 4 * Matrix.det (S : Matrix (Fin 2) (Fin 2) (K p)) *
          (Units.map M.subtype.toMonoidHom l.1 : K p) := by ring
      _ = r ^ 2 := hr.symm
  have htraceInjective : Function.Injective (fun z : X ↦
      Matrix.trace (((S * A z.1.1 : GL (Fin 2) (K p)) :
        Matrix (Fin 2) (Fin 2) (K p)))) := by
    intro z w htrace
    change Matrix.trace (((S * A z.1.1 : GL (Fin 2) (K p)) :
        Matrix (Fin 2) (Fin 2) (K p))) =
      Matrix.trace (((S * A w.1.1 : GL (Fin 2) (K p)) :
        Matrix (Fin 2) (Fin 2) (K p))) at htrace
    rw [hA z.1.1, hA w.1.1, z.2, w.2,
      DicksonWildAffine.trace_mul_affineGL,
      DicksonWildAffine.trace_mul_affineGL] at htrace
    have hfirst : (coord z.1.1).1 = (coord w.1.1).1 := by
      apply Subtype.ext
      apply mul_left_cancel₀ hS10
      linear_combination htrace
    have hcoordEq : coord z.1.1 = coord w.1.1 := by
      apply Prod.ext hfirst
      exact z.2.trans w.2.symm
    have hn : z.1.1 = w.1.1 := hcoord.1 hcoordEq
    apply Subtype.ext
    apply Subtype.ext
    exact hn
  have hxCases : Matrix.trace (((S * A x.1.1 : GL (Fin 2) (K p)) :
      Matrix (Fin 2) (Fin 2) (K p))) = r ∨
      Matrix.trace (((S * A x.1.1 : GL (Fin 2) (K p)) :
        Matrix (Fin 2) (Fin 2) (K p))) = -r :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (htraceSq x)
  rcases hxCases with hx | hx
  · exact ⟨x.1.1, x.1.2, x.2, hx⟩
  have hyCases : Matrix.trace (((S * A y.1.1 : GL (Fin 2) (K p)) :
      Matrix (Fin 2) (Fin 2) (K p))) = r ∨
      Matrix.trace (((S * A y.1.1 : GL (Fin 2) (K p)) :
        Matrix (Fin 2) (Fin 2) (K p))) = -r :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (htraceSq y)
  rcases hyCases with hy | hy
  · exact ⟨y.1.1, y.1.2, y.2, hy⟩
  exact (hxy (htraceInjective (hx.trans hy.symm))).elim

lemma dicksonWild_normalized_order_char_lift_entries_mem
    {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
    (G : Subgroup (PGL p)) [Finite G] (hpG : p ∣ Nat.card G) (P : Sylow p G)
    (m f t : ℕ) (htp : Nat.Coprime t p)
    (hPcard : Nat.card (P : Subgroup G) = p ^ m)
    (hNcard : Nat.card (Subgroup.normalizer (P : Set G)) = p ^ m * t)
    (hindex : (Subgroup.normalizer (P : Set G)).index = 1 + f * p ^ m)
    (hcount : Nat.card {g : G // g ≠ 1 ∧ g ^ p = 1} =
      (1 + f * p ^ m) * (p ^ m - 1))
    (hhalf : 2 * t = p ^ m - 1)
    (M : Subfield (K p)) [Finite M] (hMcard : Nat.card M = p ^ m)
    (L : Subgroup Mˣ) (hLcard : Nat.card L = t)
    (hLsquare : L = (powMonoidHom 2 : Mˣ →* Mˣ).range)
    (j : G →* PGL p) (hj : Function.Injective j)
    (coord : Subgroup.normalizer (P : Set G) → M × L)
    (hcoord : Function.Bijective coord)
    (hnormal : ∀ n : Subgroup.normalizer (P : Set G),
      j n.1 = Matrix.ProjGenLinGroup.map M.subtype
        (Matrix.ProjGenLinGroup.mk
          (DicksonWildAffine.affineGL (coord n).1 (coord n).2.1)))
    (hout : ∀ g : G, g ∉ Subgroup.normalizer (P : Set G) →
      ∃ S : GL (Fin 2) (K p), Matrix.ProjGenLinGroup.mk S = j g ∧
        (S : Matrix (Fin 2) (Fin 2) (K p)) 1 0 ≠ 0)
    (hq : 3 < p ^ m) (g : G) (hg : g ∉ Subgroup.normalizer (P : Set G))
    (S : GL (Fin 2) (K p)) (hS : Matrix.ProjGenLinGroup.mk S = j g)
    (htrace : Matrix.trace (S : Matrix (Fin 2) (Fin 2) (K p)) = 2)
    (hdet : Matrix.det (S : Matrix (Fin 2) (Fin 2) (K p)) = 1)
    (hS10 : (S : Matrix (Fin 2) (Fin 2) (K p)) 1 0 ≠ 0) :
    ∀ i k, (S : Matrix (Fin 2) (Fin 2) (K p)) i k ∈ M := by
  classical
  have htwo : (2 : K p) ≠ 0 := by
    apply (CharP.cast_eq_zero_iff (K p) p 2).not.mpr
    intro hpdiv
    have := Nat.le_of_dvd (by decide : 0 < 2) hpdiv
    have hpgt : 2 < p := Fact.out
    omega
  have hfour : (4 : K p) ≠ 0 := by
    rw [show (4 : K p) = 2 * 2 by norm_num]
    exact mul_ne_zero htwo htwo
  have htraceEntries : (S : Matrix (Fin 2) (Fin 2) (K p)) 0 0 + S 1 1 = 2 := by
    simpa [Matrix.trace, Fin.sum_univ_two] using htrace
  have findTrace (l : L) (r : K p)
      (hr : r ^ 2 = 4 * Matrix.det (S : Matrix (Fin 2) (Fin 2) (K p)) *
        (Units.map M.subtype.toMonoidHom l.1 : K p)) :
      ∃ n : Subgroup.normalizer (P : Set G),
        (g * (n.1 : G)) ^ p = 1 ∧ (coord n).2 = l ∧
        Matrix.trace (((S * Matrix.GeneralLinearGroup.map M.subtype
          (DicksonWildAffine.affineGL (coord n).1 (coord n).2.1) :
            GL (Fin 2) (K p)) : Matrix (Fin 2) (Fin 2) (K p))) = r :=
    dicksonWild_exists_order_char_with_multiplier_and_trace G hpG P m f t htp
      hPcard hNcard hindex hcount hhalf M L hLcard j hj coord hcoord hnormal hout
      g hg S hS hS10 l r hr
  have hnegRoot : (-2 : K p) ^ 2 =
      4 * Matrix.det (S : Matrix (Fin 2) (Fin 2) (K p)) *
        (Units.map M.subtype.toMonoidHom (1 : L).1 : K p) := by
    rw [hdet]
    norm_num
  obtain ⟨nNeg, -, hnNeg, htrNeg⟩ := findTrace 1 (-2) hnegRoot
  rw [DicksonWildAffine.affineGL_map_subfield, hnNeg,
    DicksonWildAffine.trace_mul_affineGL] at htrNeg
  have hunit : Units.map M.subtype.toMonoidHom (1 : L).1 = (1 : (K p)ˣ) := by
    exact map_one (Units.map M.subtype.toMonoidHom)
  have hunitVal : (Units.map M.subtype.toMonoidHom (1 : L).1 : K p) = 1 :=
    congrArg Units.val hunit
  rw [hunitVal, mul_one] at htrNeg
  change (S : Matrix (Fin 2) (Fin 2) (K p)) 0 0 +
      S 1 0 * ((coord nNeg).1 : K p) + S 1 1 = -2 at htrNeg
  let xNeg : M := (coord nNeg).1
  have hgammaMul : (S : Matrix (Fin 2) (Fin 2) (K p)) 1 0 * (xNeg : K p) = -4 := by
    dsimp [xNeg]
    linear_combination htrNeg - htraceEntries
  have hxNeg : (xNeg : K p) ≠ 0 := by
    intro hx
    rw [hx, mul_zero] at hgammaMul
    exact hfour (by simpa using hgammaMul.symm)
  have hgammaEq : (S : Matrix (Fin 2) (Fin 2) (K p)) 1 0 =
      (-4 : K p) / (xNeg : K p) := (eq_div_iff hxNeg).2 hgammaMul
  have hgamma : (S : Matrix (Fin 2) (Fin 2) (K p)) 1 0 ∈ M := by
    rw [hgammaEq]
    exact M.div_mem (M.neg_mem (natCast_mem M 4)) xNeg.2
  let _ : Fintype M := Fintype.ofFinite M
  obtain ⟨eta, heta0, heta1, hetaNeg1⟩ :
      ∃ eta : M, eta ≠ 0 ∧ eta ≠ 1 ∧ eta ≠ -1 := by
    by_contra hnone
    push Not at hnone
    have hsubset : (Finset.univ : Finset M) ⊆ {0, 1, -1} := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_cases hx0 : x = 0
      · exact Or.inl hx0
      by_cases hx1 : x = 1
      · exact Or.inr (Or.inl hx1)
      · exact Or.inr (Or.inr (hnone x hx0 hx1))
    have hsmall : Fintype.card M ≤ 3 := by
      calc
        Fintype.card M = (Finset.univ : Finset M).card := by simp
        _ ≤ ({0, 1, -1} : Finset M).card := Finset.card_le_card hsubset
        _ ≤ 3 := Finset.card_le_three
    rw [← Nat.card_eq_fintype_card, hMcard] at hsmall
    omega
  let etaU : Mˣ := Units.mk0 eta heta0
  have hetaSqMem : etaU ^ 2 ∈ L := by
    rw [hLsquare]
    exact ⟨etaU, rfl⟩
  let lEta : L := ⟨etaU ^ 2, hetaSqMem⟩
  have hetaRoot : (2 * (eta : K p)) ^ 2 =
      4 * Matrix.det (S : Matrix (Fin 2) (Fin 2) (K p)) *
        (Units.map M.subtype.toMonoidHom lEta.1 : K p) := by
    rw [hdet]
    simp [lEta, etaU]
    ring
  obtain ⟨nEta, -, hnEta, htrEta⟩ := findTrace lEta (2 * (eta : K p)) hetaRoot
  rw [DicksonWildAffine.affineGL_map_subfield, hnEta,
    DicksonWildAffine.trace_mul_affineGL] at htrEta
  have hetaUnitVal :
      (Units.map M.subtype.toMonoidHom (etaU ^ 2) : K p) = (eta : K p) ^ 2 := by
    rfl
  change (S : Matrix (Fin 2) (Fin 2) (K p)) 0 0 *
      (Units.map M.subtype.toMonoidHom (etaU ^ 2) : K p) +
      S 1 0 * ((coord nEta).1 : K p) + S 1 1 = 2 * (eta : K p) at htrEta
  rw [hetaUnitVal] at htrEta
  let gammaM : M := ⟨(S : Matrix (Fin 2) (Fin 2) (K p)) 1 0, hgamma⟩
  let denom : M := eta ^ 2 - 1
  let numer : M := 2 * eta - 2 - gammaM * (coord nEta).1
  have hdenom : (denom : K p) ≠ 0 := by
    intro hzero
    have hetaSq : eta ^ 2 = 1 := by
      apply Subtype.ext
      exact sub_eq_zero.mp hzero
    rcases sq_eq_one_iff.mp hetaSq with h | h
    · exact heta1 h
    · exact hetaNeg1 h
  have halphaMul : (S : Matrix (Fin 2) (Fin 2) (K p)) 0 0 * (denom : K p) =
      (numer : K p) := by
    dsimp [denom, numer, gammaM]
    calc
      (S : Matrix (Fin 2) (Fin 2) (K p)) 0 0 * ((eta : K p) ^ 2 - 1) =
          (S 0 0 * (eta : K p) ^ 2 + S 1 0 * ((coord nEta).1 : K p) + S 1 1) -
            (S 0 0 + S 1 1) - S 1 0 * ((coord nEta).1 : K p) := by ring
      _ = 2 * (eta : K p) - 2 - S 1 0 * ((coord nEta).1 : K p) := by
        rw [htrEta, htraceEntries]
  have halphaEq : (S : Matrix (Fin 2) (Fin 2) (K p)) 0 0 =
      (numer : K p) / (denom : K p) := (eq_div_iff hdenom).2 halphaMul
  have halpha : (S : Matrix (Fin 2) (Fin 2) (K p)) 0 0 ∈ M := by
    rw [halphaEq]
    exact (numer / denom).2
  have hdeltaEq : (S : Matrix (Fin 2) (Fin 2) (K p)) 1 1 =
      2 - S 0 0 := by linear_combination htraceEntries
  have hdelta : (S : Matrix (Fin 2) (Fin 2) (K p)) 1 1 ∈ M := by
    rw [hdeltaEq]
    exact M.sub_mem (natCast_mem M 2) halpha
  have hdetEntries : (S : Matrix (Fin 2) (Fin 2) (K p)) 0 0 * S 1 1 -
      S 0 1 * S 1 0 = 1 := by
    simpa [Matrix.det_fin_two] using hdet
  have hbetaMul : (S : Matrix (Fin 2) (Fin 2) (K p)) 0 1 * S 1 0 =
      S 0 0 * S 1 1 - 1 := by
    calc
      (S : Matrix (Fin 2) (Fin 2) (K p)) 0 1 * S 1 0 =
          S 0 0 * S 1 1 - (S 0 0 * S 1 1 - S 0 1 * S 1 0) := by ring
      _ = S 0 0 * S 1 1 - 1 := by rw [hdetEntries]
  have hbetaEq : (S : Matrix (Fin 2) (Fin 2) (K p)) 0 1 =
      (S 0 0 * S 1 1 - 1) / S 1 0 := (eq_div_iff hS10).2 hbetaMul
  have hbeta : (S : Matrix (Fin 2) (Fin 2) (K p)) 0 1 ∈ M := by
    rw [hbetaEq]
    exact M.div_mem (M.sub_mem (M.mul_mem halpha hdelta) (M.one_mem)) hgamma
  intro i k
  fin_cases i <;> fin_cases k
  · exact halpha
  · exact hbeta
  · exact hgamma
  · exact hdelta

set_option maxHeartbeats 800000 in
-- The containment proof instantiates the trace-fiber lemma twice in dependent subtypes.
lemma dicksonWild_range_le_embedded_psl_of_half
    {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
    (G : Subgroup (PGL p)) [Finite G] (hpG : p ∣ Nat.card G) (P : Sylow p G)
    (m f t : ℕ) (htp : Nat.Coprime t p)
    (hPcard : Nat.card (P : Subgroup G) = p ^ m)
    (hNcard : Nat.card (Subgroup.normalizer (P : Set G)) = p ^ m * t)
    (hindex : (Subgroup.normalizer (P : Set G)).index = 1 + f * p ^ m)
    (hcount : Nat.card {g : G // g ≠ 1 ∧ g ^ p = 1} =
      (1 + f * p ^ m) * (p ^ m - 1))
    (hhalf : 2 * t = p ^ m - 1)
    (M : Subfield (K p)) [Finite M] (hMcard : Nat.card M = p ^ m)
    (L : Subgroup Mˣ) (hLcard : Nat.card L = t)
    (j : G →* PGL p) (hj : Function.Injective j)
    (coord : Subgroup.normalizer (P : Set G) → M × L)
    (hcoord : Function.Bijective coord)
    (hnormal : ∀ n : Subgroup.normalizer (P : Set G),
      j n.1 = Matrix.ProjGenLinGroup.map M.subtype
        (Matrix.ProjGenLinGroup.mk
          (DicksonWildAffine.affineGL (coord n).1 (coord n).2.1)))
    (hout : ∀ g : G, g ∉ Subgroup.normalizer (P : Set G) →
      ∃ S : GL (Fin 2) (K p), Matrix.ProjGenLinGroup.mk S = j g ∧
        (S : Matrix (Fin 2) (Fin 2) (K p)) 1 0 ≠ 0)
    (hq : 3 < p ^ m) :
    j.range ≤ ((Matrix.ProjGenLinGroup.map M.subtype).comp
      Matrix.ProjectiveSpecialLinearGroup.toPGL).range := by
  classical
  let N := Subgroup.normalizer (P : Set G)
  let pslEmbed : Matrix.ProjectiveSpecialLinearGroup (Fin 2) M →* PGL p :=
    (Matrix.ProjGenLinGroup.map M.subtype).comp
      Matrix.ProjectiveSpecialLinearGroup.toPGL
  have hLsquare : L = (powMonoidHom 2 : Mˣ →* Mˣ).range :=
    DicksonWildAffine.subgroup_eq_square_range_of_card L (p ^ m) t hMcard hLcard hhalf
  have hNmem (n : N) : j n.1 ∈ pslEmbed.range := by
    have hl : (coord n).2.1 ∈ (powMonoidHom 2 : Mˣ →* Mˣ).range := by
      rw [← hLsquare]
      exact (coord n).2.2
    obtain ⟨v, hv⟩ := hl
    have hv' : v ^ 2 = (coord n).2.1 := by simpa using hv
    have hdetAff : v ^ 2 = Matrix.GeneralLinearGroup.det
        (DicksonWildAffine.affineGL (coord n).1 (coord n).2.1) := by
      rw [hv']
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.val_det_apply]
      simp [DicksonWildAffine.affineGL, Matrix.det_fin_two]
    obtain ⟨z, hz⟩ := dicksonWild_exists_psl_preimage_of_det_square
      (DicksonWildAffine.affineGL (coord n).1 (coord n).2.1) v hdetAff
    refine ⟨z, ?_⟩
    change Matrix.ProjGenLinGroup.map M.subtype
      (Matrix.ProjectiveSpecialLinearGroup.toPGL z) = j n.1
    rw [hz, hnormal n]
  rintro y ⟨g, rfl⟩
  by_cases hg : g ∈ N
  · exact hNmem ⟨g, hg⟩
  · have hfiber : Nat.card {n : {n : N // (g * (n.1 : G)) ^ p = 1} //
        (coord n.1).2 = 1} = 2 :=
      dicksonWild_card_order_char_with_multiplier_eq_two G hpG P m f t htp
        hPcard hNcard hindex hcount hhalf M L hLcard j hj coord hcoord hnormal hout
          g hg 1
    have hnonempty : Nonempty {n : {n : N // (g * (n.1 : G)) ^ p = 1} //
        (coord n.1).2 = 1} :=
      (Nat.card_pos_iff.mp (by rw [hfiber]; omega)).1
    obtain ⟨w⟩ := hnonempty
    let n : N := w.1.1
    let z : G := g * (n.1 : G)
    have hzpow : z ^ p = 1 := w.1.2
    have hzOut : z ∉ N := by
      intro hzN
      apply hg
      have hgeq : g = z * (n.1 : G)⁻¹ := by dsimp [z]; group
      rw [hgeq]
      exact N.mul_mem hzN (N.inv_mem n.2)
    have hzNe : z ≠ 1 := by
      intro hz
      apply hzOut
      rw [hz]
      exact N.one_mem
    have hzOrder : orderOf z = p := orderOf_eq_prime hzpow hzNe
    obtain ⟨S₀, hS₀, hS₀10⟩ := hout z hzOut
    have hS₀Order : orderOf (Matrix.ProjGenLinGroup.mk S₀) = p := by
      rw [hS₀]
      exact (orderOf_injective j hj z).trans hzOrder
    obtain ⟨S, hSmk, hStrace, hSdet, hS10⟩ :=
      dicksonWild_exists_normalized_lift_of_orderOf_eq_char S₀ hS₀Order hS₀10
    have hSj : Matrix.ProjGenLinGroup.mk S = j z := hSmk.trans hS₀
    have hentries := dicksonWild_normalized_order_char_lift_entries_mem
      G hpG P m f t htp hPcard hNcard hindex hcount hhalf M hMcard L hLcard
      hLsquare j hj coord hcoord hnormal hout hq z hzOut S hSj hStrace hSdet hS10
    obtain ⟨s, hs⟩ :=
      dicksonWild_exists_embedded_psl_preimage_of_entries_mem M S hentries hSdet
    have hzMem : j z ∈ pslEmbed.range := by
      refine ⟨s, ?_⟩
      exact hs.trans hSj
    have hnMem : j n.1 ∈ pslEmbed.range := hNmem n
    have hjg : j g = j z * (j n.1)⁻¹ := by
      dsimp [z]
      rw [map_mul]
      group
    rw [hjg]
    exact pslEmbed.range.mul_mem hzMem (pslEmbed.range.inv_mem hnMem)

lemma dicksonWild_psl_case_of_half_gt_three
    {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
    (G : Subgroup (PGL p)) [Finite G] (hpG : p ∣ Nat.card G) (P : Sylow p G)
    (m f t : ℕ) (hm : 1 ≤ m) (hf : 0 < f) (htp : Nat.Coprime t p)
    (hPcard : Nat.card (P : Subgroup G) = p ^ m)
    (hNcard : Nat.card (Subgroup.normalizer (P : Set G)) = p ^ m * t)
    (hindex : (Subgroup.normalizer (P : Set G)).index = 1 + f * p ^ m)
    (hcount : Nat.card {g : G // g ≠ 1 ∧ g ^ p = 1} =
      (1 + f * p ^ m) * (p ^ m - 1))
    (hhalf : 2 * t = p ^ m - 1) (hq : 3 < p ^ m) :
    Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p m)) := by
  classical
  have hsandwich : p ^ m - 1 ≤ 2 * t := hhalf.ge
  obtain ⟨M, L, j, coord, hMfinite, hMcard, hLcard, hj, hcoord, hnormal, hout⟩ :=
    dicksonWild_exists_matrix_normal_form G hpG P m t hm htp hNcard hsandwich
  let _ : Finite M := hMfinite
  let _ : Fintype M := Fintype.ofFinite M
  let pslEmbed : Matrix.ProjectiveSpecialLinearGroup (Fin 2) M →* PGL p :=
    (Matrix.ProjGenLinGroup.map M.subtype).comp
      Matrix.ProjectiveSpecialLinearGroup.toPGL
  have hpslInjective : Function.Injective pslEmbed :=
    (projGenLinGroup_map_injective M.subtype M.subtype_injective).comp
      Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  let J : Subgroup (PGL p) := j.range
  let H : Subgroup (PGL p) := pslEmbed.range
  have hJfinite : Finite J := Finite.of_surjective j.rangeRestrict
    j.rangeRestrict_surjective
  let _ : Finite J := hJfinite
  have hHfinite : Finite H := Finite.of_surjective pslEmbed.rangeRestrict
    pslEmbed.rangeRestrict_surjective
  let _ : Finite H := hHfinite
  have hle : J ≤ H :=
    dicksonWild_range_le_embedded_psl_of_half G hpG P m f t htp hPcard hNcard
      hindex hcount hhalf M hMcard L hLcard j hj coord hcoord hnormal hout hq
  have hp2 : p ≠ 2 := by
    have hpgt : 2 < p := Fact.out
    omega
  have hqeq : p ^ m = 2 * t + 1 := by omega
  have hquad : (p ^ m) ^ 2 - 1 = 2 * (t * (p ^ m + 1)) := by
    rw [hqeq]
    have hring : (2 * t + 1) ^ 2 = 2 * (t * (2 * t + 1 + 1)) + 1 := by ring
    omega
  have hHcard : Nat.card H = p ^ m * t * (p ^ m + 1) := by
    calc
      Nat.card H = Nat.card
          (Matrix.ProjectiveSpecialLinearGroup (Fin 2) M) :=
        Nat.card_congr (MonoidHom.ofInjective hpslInjective).symm.toEquiv
      _ = Nat.card M * (Nat.card M ^ 2 - 1) / 2 := by
        rw [card_projectiveSpecialLinearGroup_fin_two p M hp2,
          Nat.card_eq_fintype_card]
      _ = p ^ m * ((p ^ m) ^ 2 - 1) / 2 := by rw [hMcard]
      _ = p ^ m * t * (p ^ m + 1) := by
        rw [hquad]
        rw [show p ^ m * (2 * (t * (p ^ m + 1))) =
          2 * (p ^ m * t * (p ^ m + 1)) by ring]
        exact Nat.mul_div_cancel_left _ (by omega)
  have hGcard : Nat.card G = p ^ m * t * (1 + f * p ^ m) := by
    have hprod := (Subgroup.normalizer (P : Set G)).card_mul_index
    rw [hNcard, hindex] at hprod
    exact hprod.symm
  have hJcard : Nat.card J = p ^ m * t * (1 + f * p ^ m) := by
    rw [← hGcard]
    exact (Nat.card_congr (MonoidHom.ofInjective hj).toEquiv).symm
  have hcardLe : Nat.card J ≤ Nat.card H :=
    Nat.card_le_card_of_injective (Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
  rw [hJcard, hHcard] at hcardLe
  have hfactorPos : 0 < p ^ m * t := by
    have ht : 0 < t := by
      have hpPow : 3 < p ^ m := hq
      omega
    exact mul_pos (pow_pos (Fact.out : p.Prime).pos m) ht
  have honeLe : 1 + f * p ^ m ≤ p ^ m + 1 := by
    apply Nat.le_of_mul_le_mul_left (c := p ^ m * t)
    · simpa [mul_assoc] using hcardLe
    · exact hfactorPos
  have hfmul : f * p ^ m ≤ 1 * p ^ m := by omega
  have hfle : f ≤ 1 := Nat.le_of_mul_le_mul_right hfmul (pow_pos (Fact.out : p.Prime).pos m)
  have hf1 : f = 1 := by omega
  have hcardEq : Nat.card J = Nat.card H := by
    rw [hJcard, hHcard, hf1]
    ring
  let incl : J →* H := Subgroup.inclusion hle
  have hincl : Function.Bijective incl := by
    let _ : Fintype J := Fintype.ofFinite J
    let _ : Fintype H := Fintype.ofFinite H
    apply (Fintype.bijective_iff_injective_and_card incl).2
    exact ⟨Subgroup.inclusion_injective hle, by
      simpa only [← Nat.card_eq_fintype_card] using hcardEq⟩
  have hge : H ≤ J := by
    intro x hx
    obtain ⟨y, hy⟩ := hincl.2 ⟨x, hx⟩
    have hval : (y.1 : PGL p) = x := congrArg Subtype.val hy
    rw [← hval]
    exact y.2
  have hJH : J = H := le_antisymm hle hge
  let eJ : G ≃* J := MonoidHom.ofInjective hj
  let eH : Matrix.ProjectiveSpecialLinearGroup (Fin 2) M ≃* H :=
    MonoidHom.ofInjective hpslInjective
  let eJH : J ≃* H :=
    MulEquiv.cast (M := fun Q : Subgroup (PGL p) ↦ Q) hJH
  let eJM : G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) M :=
    eJ.trans (eJH.trans eH.symm)
  let _ : Algebra (ZMod p) M := ZMod.algebra M p
  let eField : M ≃ₐ[ZMod p] GaloisField p m :=
    GaloisField.algEquivGaloisField p m hMcard
  exact ⟨eJM.trans
    (dicksonWild_projectiveSpecialLinearGroup_congr eField.toRingEquiv)⟩

lemma dicksonWild_pgl_case_of_full
    {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
    (G : Subgroup (PGL p)) [Finite G] (hpG : p ∣ Nat.card G) (P : Sylow p G)
    (m t : ℕ) (hm : 1 ≤ m) (htp : Nat.Coprime t p)
    (hNcard : Nat.card (Subgroup.normalizer (P : Set G)) = p ^ m * t)
    (hindex : (Subgroup.normalizer (P : Set G)).index = 1 + p ^ m)
    (hfull : t = p ^ m - 1) :
    Nonempty (G ≃* Matrix.ProjGenLinGroup (Fin 2) (GaloisField p m)) := by
  classical
  have hsandwich : p ^ m - 1 ≤ 2 * t := by omega
  obtain ⟨M, L, j, coord, hMfinite, hMcard, hLcard, hj, hcoord, hnormal, hout⟩ :=
    dicksonWild_exists_matrix_normal_form G hpG P m t hm htp hNcard hsandwich
  let _ : Finite M := hMfinite
  let _ : Fintype M := Fintype.ofFinite M
  obtain ⟨κ, hle⟩ :=
    dicksonWild_exists_conjugate_range_le_embedded_pgl_of_index_eq
      G P m M hMcard L j coord hindex hcoord hnormal hout
  let j' : G →* PGL p := (MulAut.conj κ).toMonoidHom.comp j
  have hj' : Function.Injective j' := (MulAut.conj κ).injective.comp hj
  let pglEmbed : Matrix.ProjGenLinGroup (Fin 2) M →* PGL p :=
    Matrix.ProjGenLinGroup.map M.subtype
  have hpglInjective : Function.Injective pglEmbed :=
    projGenLinGroup_map_injective M.subtype M.subtype_injective
  let J : Subgroup (PGL p) := j'.range
  let H : Subgroup (PGL p) := pglEmbed.range
  have hJfinite : Finite J := Finite.of_surjective j'.rangeRestrict
    j'.rangeRestrict_surjective
  let _ : Finite J := hJfinite
  let _ : Finite (Matrix.ProjGenLinGroup (Fin 2) M) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk
      Matrix.ProjGenLinGroup.mk_surjective
  have hHfinite : Finite H := Finite.of_surjective pglEmbed.rangeRestrict
    pglEmbed.rangeRestrict_surjective
  let _ : Finite H := hHfinite
  have hHcard : Nat.card H = p ^ m * ((p ^ m) ^ 2 - 1) := by
    calc
      Nat.card H = Nat.card (Matrix.ProjGenLinGroup (Fin 2) M) :=
        Nat.card_congr (MonoidHom.ofInjective hpglInjective).symm.toEquiv
      _ = Fintype.card M * (Fintype.card M ^ 2 - 1) :=
        card_projGenLinGroup_fin_two M
      _ = p ^ m * ((p ^ m) ^ 2 - 1) := by
        rw [← Nat.card_eq_fintype_card, hMcard]
  have hGcard : Nat.card G = p ^ m * t * (1 + p ^ m) := by
    have hprod := (Subgroup.normalizer (P : Set G)).card_mul_index
    rw [hNcard, hindex] at hprod
    exact hprod.symm
  have hJcard : Nat.card J = p ^ m * t * (1 + p ^ m) := by
    rw [← hGcard]
    exact (Nat.card_congr (MonoidHom.ofInjective hj').toEquiv).symm
  have hqone : 1 ≤ p ^ m := one_le_pow₀ (Fact.out : p.Prime).one_lt.le
  have hfactor : (p ^ m) ^ 2 - 1 = (p ^ m - 1) * (p ^ m + 1) := by
    have hqeq : p ^ m = (p ^ m - 1) + 1 := by omega
    rw [Nat.sub_eq_iff_eq_add (one_le_pow₀ hqone)]
    nlinarith
  have hcardEq : Nat.card J = Nat.card H := by
    rw [hJcard, hHcard, hfull, hfactor]
    ring
  let incl : J → H := Subgroup.inclusion hle
  have hincl : Function.Bijective incl := by
    let _ : Fintype J := Fintype.ofFinite J
    let _ : Fintype H := Fintype.ofFinite H
    apply (Fintype.bijective_iff_injective_and_card incl).2
    exact ⟨Subgroup.inclusion_injective hle, by
      simpa only [← Nat.card_eq_fintype_card] using hcardEq⟩
  have hge : H ≤ J := by
    intro x hx
    obtain ⟨y, hy⟩ := hincl.2 ⟨x, hx⟩
    have hval : (y.1 : PGL p) = x := congrArg Subtype.val hy
    rw [← hval]
    exact y.2
  have hJH : J = H := le_antisymm hle hge
  let eJ : G ≃* J := MonoidHom.ofInjective hj'
  let eH : Matrix.ProjGenLinGroup (Fin 2) M ≃* H :=
    MonoidHom.ofInjective hpglInjective
  let eJH : J ≃* H := MulEquiv.cast (M := fun Q : Subgroup (PGL p) ↦ Q) hJH
  let eJM : G ≃* Matrix.ProjGenLinGroup (Fin 2) M :=
    eJ.trans (eJH.trans eH.symm)
  let _ : Algebra (ZMod p) M := ZMod.algebra M p
  let eField : M ≃ₐ[ZMod p] GaloisField p m :=
    GaloisField.algEquivGaloisField p m hMcard
  exact ⟨eJM.trans (dicksonWild_projGenLinGroup_congr eField.toRingEquiv)⟩

lemma dicksonWild_psl_case_of_half_eq_three
    {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
    (G : Subgroup (PGL p)) [Finite G] (hpG : p ∣ Nat.card G) (P : Sylow p G)
    (m t : ℕ) (hm : 1 ≤ m) (htp : Nat.Coprime t p)
    (hNcard : Nat.card (Subgroup.normalizer (P : Set G)) = p ^ m * t)
    (hindex : (Subgroup.normalizer (P : Set G)).index = 1 + p ^ m)
    (hhalf : 2 * t = p ^ m - 1) (hq3 : p ^ m = 3) :
    Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2)
      (GaloisField p m)) := by
  classical
  have hsandwich : p ^ m - 1 ≤ 2 * t := hhalf.ge
  obtain ⟨M, L, j, coord, hMfinite, hMcard, hLcard, hj, hcoord, hnormal, hout⟩ :=
    dicksonWild_exists_matrix_normal_form G hpG P m t hm htp hNcard hsandwich
  let _ : Finite M := hMfinite
  let _ : Fintype M := Fintype.ofFinite M
  obtain ⟨κ, hle⟩ :=
    dicksonWild_exists_conjugate_range_le_embedded_pgl_of_index_eq
      G P m M hMcard L j coord hindex hcoord hnormal hout
  let j' : G →* PGL p := (MulAut.conj κ).toMonoidHom.comp j
  have hj' : Function.Injective j' := (MulAut.conj κ).injective.comp hj
  let pglEmbed : Matrix.ProjGenLinGroup (Fin 2) M →* PGL p :=
    Matrix.ProjGenLinGroup.map M.subtype
  have hpglInjective : Function.Injective pglEmbed :=
    projGenLinGroup_map_injective M.subtype M.subtype_injective
  let J : Subgroup (PGL p) := j'.range
  let H : Subgroup (PGL p) := pglEmbed.range
  let eJ : G ≃* J := MonoidHom.ofInjective hj'
  let eH : Matrix.ProjGenLinGroup (Fin 2) M ≃* H :=
    MonoidHom.ofInjective hpglInjective
  let incl : J →* H := Subgroup.inclusion hle
  let toPGL : J →* Matrix.ProjGenLinGroup (Fin 2) M :=
    eH.symm.toMonoidHom.comp incl
  have htoPGL : Function.Injective toPGL :=
    eH.symm.injective.comp (Subgroup.inclusion_injective hle)
  have ht1 : t = 1 := by omega
  have hGcard : Nat.card G = 12 := by
    have hprod := (Subgroup.normalizer (P : Set G)).card_mul_index
    rw [hNcard, hindex, hq3, ht1] at hprod
    norm_num at hprod ⊢
    exact hprod.symm
  have hJfinite : Finite J := Finite.of_surjective eJ eJ.surjective
  let _ : Finite J := hJfinite
  have hJcard : Nat.card J = 12 := by
    rw [← hGcard]
    exact (Nat.card_congr eJ.toEquiv).symm
  let X := Projectivization M (Fin 2 → M)
  let _ : Fintype X := Fintype.ofEquiv (OnePoint M)
    (OnePoint.equivProjectivization M)
  have hMcard3 : Nat.card M = 3 := hMcard.trans hq3
  have hOneCard : Fintype.card (OnePoint M) = 4 := by
    change Fintype.card (Option M) = 4
    rw [Fintype.card_option, ← Nat.card_eq_fintype_card, hMcard3]
  have hXcard : Fintype.card X = 4 := by
    calc
      Fintype.card X = Fintype.card (OnePoint M) :=
        (Fintype.card_congr (OnePoint.equivProjectivization M)).symm
      _ = 4 := hOneCard
  let eFin : X ≃ Fin 4 := (Fintype.equivFin X).trans (finCongr hXcard)
  let pglAct : Matrix.ProjGenLinGroup (Fin 2) M →* Equiv.Perm (Fin 4) :=
    eFin.permCongrHom.toMonoidHom.comp
      (MulAction.toPermHom (Matrix.ProjGenLinGroup (Fin 2) M) X)
  have hpglAct : Function.Injective pglAct := eFin.permCongrHom.injective.comp
    dicksonWild_pgl_toPermHom_injective
  let act : J →* Equiv.Perm (Fin 4) := pglAct.comp toPGL
  have hact : Function.Injective act := hpglAct.comp htoPGL
  have hPermCard : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    norm_num [Nat.factorial]
  have hactIndex : act.range.index = 2 :=
    dicksonWild_perm_range_index_eq_two_of_card act hact 12 hJcard (by omega)
  obtain ⟨eJAlt⟩ :=
    dicksonWild_mulEquiv_alternating_of_perm_index_two act hact hactIndex
  have hp2 : p ≠ 2 := by
    have hpgt : 2 < p := Fact.out
    omega
  obtain ⟨ePSLAlt⟩ :=
    dicksonWild_psl_card_three_equiv_alternating_four p M hp2 hMcard3
  let eJM : G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) M :=
    eJ.trans (eJAlt.trans ePSLAlt.symm)
  let _ : Algebra (ZMod p) M := ZMod.algebra M p
  let eField : M ≃ₐ[ZMod p] GaloisField p m :=
    GaloisField.algEquivGaloisField p m hMcard
  exact ⟨eJM.trans
    (dicksonWild_projectiveSpecialLinearGroup_congr eField.toRingEquiv)⟩

/-- **Dickson's classification**, wild case: a finite subgroup of `PGL₂` over
an algebraic closure of `𝔽_p` (odd `p`), of order divisible by `p`, is a
Frobenius group with a faithful action that fixes no nonzero vector, `PSL₂` or
`PGL₂` over a finite subfield, or (for `p = 3`) `A₅`. The first alternative
records the group-theoretic consequences of the scalar-root action rather than
constructing the scalar embedding itself.

Source: L. E. Dickson, *Linear Groups with an Exposition of the Galois Field
Theory*, Teubner (1901).

Proves `Wanted` entry `classification_wild`.

Proof: We follow X. Faber, *Finite p-irregular subgroups of PGL₂(k)*,
arXiv:1112.1999, §6, using the Sylow normal form, exceptional-orbit count, and projective-line
actions to identify the `PSL₂`, `PGL₂`, and `A₅` cases.
-/
theorem classification_wild (G : Subgroup (PGL p)) [Finite G]
    (hG_p : p ∣ Nat.card G) :
    (∃ (m t : ℕ) (_ : m ≥ 1) (_ : Nat.Coprime t p) (_ : t ∣ p ^ m - 1)
      (φ : Multiplicative (ZMod t) →* MulAut (Multiplicative (Fin m → ZMod p)))
      (_hφ_injective : Function.Injective φ)
      (_hφ_fixed_point_free : ∀ c ≠ 1, ∀ v ≠ 1, φ c v ≠ v),
      Nonempty (G ≃* (Multiplicative (Fin m → ZMod p)) ⋊[φ] Multiplicative (ZMod t))) ∨
    (∃ m : ℕ, m ≥ 1 ∧
      Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p m))) ∨
    (∃ m : ℕ, m ≥ 1 ∧
      Nonempty (G ≃* Matrix.ProjGenLinGroup (Fin 2) (GaloisField p m))) ∨
    (p = 3 ∧ Nonempty (G ≃* alternatingGroup (Fin 5))) := by
  let P : Sylow p G := Classical.choice inferInstance
  by_cases hPnormal : (P : Subgroup G).Normal
  · exact Or.inl (dicksonWild_frobenius_case_of_normal_sylow G hG_p P hPnormal)
  · obtain ⟨m, f, hm, hPcard, hf, hSylowCard, hpCount⟩ :=
      dicksonWild_order_char_count G hG_p P hPnormal
    obtain ⟨mN, t, hmN, htp, htdiv, hPcardN, hNcard⟩ :=
      dicksonWild_normalizer_order_data G hG_p P
    have hmEq : mN = m := by
      apply (Nat.pow_right_inj (Fact.out : p.Prime).one_lt).mp
      exact hPcardN.symm.trans hPcard
    subst mN
    have hindex : (Subgroup.normalizer (P : Set G)).index = 1 + f * p ^ m :=
      (P.card_eq_index_normalizer.symm.trans hSylowCard)
    have hsandwich : p ^ m - 1 ≤ 2 * t :=
      dicksonWild_sandwich_bound G hG_p P m f t hf htp hPcard hNcard
        hindex hpCount
    have hqpos : 0 < p ^ m - 1 := by
      have hpPow : 1 < p ^ m := one_lt_pow₀ (Fact.out : p.Prime).one_lt (by omega)
      omega
    have htpos : 0 < t := by
      by_contra ht
      have ht0 : t = 0 := Nat.eq_zero_of_not_pos ht
      rw [ht0, mul_zero] at hNcard
      exact Nat.card_pos.ne' hNcard
    have htCases : t = p ^ m - 1 ∨ 2 * t = p ^ m - 1 :=
      dicksonWild_eq_or_two_mul_eq_of_dvd_of_le (p ^ m - 1) t hqpos htpos
        htdiv hsandwich
    obtain ⟨M, L, j, coord, hMfinite, hMcard, hLcard, hj, hcoord, hnormal, hout⟩ :=
      dicksonWild_exists_matrix_normal_form G hG_p P m t hm htp hNcard hsandwich
    let _ : Finite M := hMfinite
    obtain ⟨d, hd, hrelation, hstabilizerLarge, hstabilizerSmall,
      hstabilizers, hexceptionalOrbits⟩ :=
      dicksonWild_exceptional_orbit_data G P m f t hm hf hNcard hindex hpCount
        M L j hj coord hnormal hout
    have hp3 : 3 ≤ p := by
      have hpgt : 2 < p := Fact.out
      omega
    have hq3 : 3 ≤ p ^ m :=
      hp3.trans (Nat.le_pow (a := p) (b := m) hm)
    rcases htCases with hfull | hhalf
    · rcases dicksonWild_f_eq_one_or_exceptional_of_full_multiplier_relation
          (p ^ m) f t d hq3 hf hfull hrelation with hf1 | hexceptional
      · subst f
        have hindex1 : (Subgroup.normalizer (P : Set G)).index = 1 + p ^ m := by
          simpa using hindex
        exact Or.inr (Or.inr (Or.inl ⟨m, hm,
          dicksonWild_pgl_case_of_full G hG_p P m t hm htp hNcard hindex1 hfull⟩))
      · obtain ⟨hqEq, hfEq⟩ := hexceptional
        subst f
        let _ : MulAction G (Projectivization (K p) (Fin 2 → K p)) :=
          MulAction.compHom _ j
        have hpEq : p = 3 := by
          have hpLe : p ≤ p ^ m := Nat.le_pow hm
          omega
        have hdEq : d = 5 := by
          rw [hfull, hqEq] at hrelation
          norm_num at hrelation
          omega
        have hqt : p ^ m * t = 6 := by rw [hfull, hqEq]
        obtain ⟨x₆, hx₆⟩ := hstabilizerLarge
        obtain ⟨x₅, hx₅⟩ := hstabilizerSmall
        have hx₆' : Nat.card (MulAction.stabilizer G x₆) = 6 := hx₆.trans hqt
        have hx₅' : Nat.card (MulAction.stabilizer G x₅) = 5 := hx₅.trans hdEq
        have hall :
            ∀ x : dicksonWildExceptional G
                (Projectivization (K p) (Fin 2 → K p)),
              Nat.card (MulAction.stabilizer G x) = 6 ∨
              Nat.card (MulAction.stabilizer G x) = 5 := by
          intro x
          rcases hstabilizers x with h | h
          · exact Or.inl (h.trans hqt)
          · exact Or.inr (h.trans hdEq)
        have hGcard : Nat.card G = 60 := by
          have hprod := (Subgroup.normalizer (P : Set G)).card_mul_index
          rw [hNcard, hindex, hfull, hqEq] at hprod
          norm_num at hprod ⊢
          omega
        have hPcardThree : Nat.card (P : Subgroup G) = 3 := hPcard.trans hqEq
        exact Or.inr (Or.inr (Or.inr ⟨hpEq,
          dicksonWild_a5_case_of_exceptional G hpEq P hPnormal hPcardThree
            j hj hGcard x₆ x₅ hx₆' hx₅' hall hexceptionalOrbits⟩))
    · have hf1 := dicksonWild_f_eq_one_of_half_multiplier_relation
          (p ^ m) f t d hq3 hf hhalf hrelation
      subst f
      have hindex1 : (Subgroup.normalizer (P : Set G)).index = 1 + p ^ m := by
        simpa using hindex
      by_cases hqgt : 3 < p ^ m
      · exact Or.inr (Or.inl ⟨m, hm,
          dicksonWild_psl_case_of_half_gt_three G hG_p P m 1 t hm (by omega)
            htp hPcard hNcard (by simpa using hindex1) (by simpa using hpCount) hhalf hqgt⟩)
      · have hqEq : p ^ m = 3 := by omega
        exact Or.inr (Or.inl ⟨m, hm,
          dicksonWild_psl_case_of_half_eq_three G hG_p P m t hm htp hNcard
            hindex1 hhalf hqEq⟩)

end Dickson
end MetaMathlibExt
