/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/WittMultigradedDimension.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.LinearAlgebra.Dimension.Finite
import Def.Algebra.Lie.FreeLieMultihomogeneousComponent
import Def.Algebra.Lie.WittMultigradedValue
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.List.Lex
import Mathlib.Data.List.Rotate
import Theorem.Combinatorics.Words.LyndonWord.Part14
import Lemma.Finset.Words.LyndonWord
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FreeAlgebra
import Instance.Algebra.Lie.WittMultigradedDimension.Part2
open scoped BigOperators

/-!
# Witt's multigraded dimension formula

This file proves the multigraded dimension formula for a finitely generated free Lie algebra,
using the Lyndon-word basis and the enumeration of Lyndon words with prescribed content.
-/


namespace MetaMathlibExt

attribute [local instance 100] LieRing.ofAssociativeRing

theorem wittLt_append_self_of_ne_nil {α : Type*} [LinearOrder α]
    (u : List α) {v : List α} (hv : v ≠ []) : u < u ++ v := by
  apply lt_of_le_of_ne (wittLe_append_self u v)
  intro h
  have hv0 := List.length_pos_of_ne_nil hv
  have := congr_arg List.length h
  simp only [List.length_append] at this
  omega

theorem wittOrderedBracket_mem_spanFrom_aux (K : Type) [Field K] {r : ℕ}
    (n : ℕ) (u v : List (Fin r)) (hu : IsLyndonWord u) (hv : IsLyndonWord v)
    (huv : u < v) (hlen : u.length + v.length = n) :
    ⁅wittLyndonBracket K u hu, wittLyndonBracket K v hv⁆ ∈
      wittLyndonSpanFrom K (wittWordContent (u ++ v)) (u ++ v) := by
  induction n using Nat.strong_induction_on generalizing u v with
  | h n ih =>
      let p0 : WittLyndonPair r n := ⟨(u, v), hu, hv, huv, hlen⟩
      have hall : ∀ p : WittLyndonPair r n,
          ⁅wittLyndonBracket K p.1.1 p.2.1,
              wittLyndonBracket K p.1.2 p.2.2.1⁆ ∈
            wittLyndonSpanFrom K (wittWordContent (p.1.1 ++ p.1.2))
              (p.1.1 ++ p.1.2) := by
        intro p
        induction p using wittLyndonPairRel_wellFounded.induction with
        | h p rec =>
            let u := p.1.1
            let v := p.1.2
            have hu : IsLyndonWord u := p.2.1
            have hv : IsLyndonWord v := p.2.2.1
            have huv : u < v := p.2.2.2.1
            have huvlen : u.length + v.length = n := p.2.2.2.2
            change ⁅wittLyndonBracket K u hu, wittLyndonBracket K v hv⁆ ∈
              wittLyndonSpanFrom K (wittWordContent (u ++ v)) (u ++ v)
            by_cases hu1 : u.length = 1
            · let hw : IsLyndonWord (u ++ v) := (wittLyndon_iff_suffix (u ++ v)).mpr
                (wittSuffixLyndon_append ((wittLyndon_iff_suffix u).mp hu)
                  ((wittLyndon_iff_suffix v).mp hv) huv)
              have heq := wittLyndonBracket_append_of_length_one K hu hv huv hu1
              exact heq ▸ wittLyndonBracket_mem_spanFrom K hw rfl le_rfl
            · have hu2 : 2 ≤ u.length := by
                have hu0 := List.length_pos_of_ne_nil hu.1
                omega
              let a := wittLongestLyndonPrefix u hu2
              let b := wittLongestLyndonSuffix u hu2
              have hfac := wittStandardFactorization hu hu2
              have huab : u = a ++ b := wittLongestLyndon_append u hu2
              have ha : IsLyndonWord a := hfac.1
              have hb : IsLyndonWord b := hfac.2.1
              have hab : a < b := hfac.2.2
              by_cases hvb : v ≤ b
              · let hw : IsLyndonWord (u ++ v) := (wittLyndon_iff_suffix (u ++ v)).mpr
                  (wittSuffixLyndon_append ((wittLyndon_iff_suffix u).mp hu)
                    ((wittLyndon_iff_suffix v).mp hv) huv)
                have heq := wittLyndonBracket_append K hu hv huv hu2 hvb
                exact heq ▸ wittLyndonBracket_mem_spanFrom K hw rfl le_rfl
              · have hbv : b < v := lt_of_not_ge hvb
                have ha0 := List.length_pos_of_ne_nil ha.1
                have hb0 := List.length_pos_of_ne_nil hb.1
                have hPu : wittLyndonBracket K u hu =
                    ⁅wittLyndonBracket K a ha, wittLyndonBracket K b hb⁆ := by
                  rw [wittLyndonBracket]
                  simp only [dite_eq_right hu1]
                  congr 1
                have hbn : b.length + v.length < n := by
                  have hul := congr_arg List.length huab
                  simp only [List.length_append] at hul
                  omega
                have hbvsp := ih (b.length + v.length) hbn b v hb hv hbv rfl
                have hau : a < u := by
                  rw [huab]
                  exact wittLt_append_self_of_ne_nil a hb.1
                have hav : a < v := hau.trans huv
                have han : a.length + v.length < n := by
                  have hul := congr_arg List.length huab
                  simp only [List.length_append] at hul
                  omega
                have havsp := ih (a.length + v.length) han a v ha hv hav rfl
                have hterm1 :
                    ⁅wittLyndonBracket K a ha,
                      ⁅wittLyndonBracket K b hb, wittLyndonBracket K v hv⁆⁆ ∈
                      wittLyndonSpanFrom K (wittWordContent (u ++ v)) (u ++ v) := by
                  change ⁅wittLyndonBracket K b hb, wittLyndonBracket K v hv⁆ ∈
                    Submodule.span K {x | ∃ (w : List (Fin r)) (hw : IsLyndonWord w),
                      wittWordContent w = wittWordContent (b ++ v) ∧ b ++ v ≤ w ∧
                        x = wittLyndonBracket K w hw} at hbvsp
                  refine Submodule.span_induction (p := fun x _ =>
                    ⁅wittLyndonBracket K a ha, x⁆ ∈
                      wittLyndonSpanFrom K (wittWordContent (u ++ v)) (u ++ v))
                    ?_ ?_ ?_ ?_ hbvsp
                  · exact by
                      intro x hx
                      rcases hx with ⟨z, hz, hzcontent, hbvz, rfl⟩
                      have haz : a < z := hab.trans_le
                        ((wittLe_append_self b v).trans hbvz)
                      have hzlen : z.length = (b ++ v).length :=
                        wittWordContent_eq_length_eq hzcontent
                      have hazlen : a.length + z.length = n := by
                        have hul := congr_arg List.length huab
                        simp only [List.length_append] at hul hzlen ⊢
                        omega
                      let q : WittLyndonPair r n := ⟨(a, z), ha, hz, haz, hazlen⟩
                      have hle : u ++ v ≤ a ++ z := by
                        rw [huab, List.append_assoc]
                        exact wittAppend_le_append_of_le_of_le le_rfl rfl hbvz
                      have halen : a.length < u.length := by
                        have hul := congr_arg List.length huab
                        simp only [List.length_append] at hul
                        omega
                      have hrel : WittLyndonPairRel q p := by
                        rcases hle.eq_or_lt with heq | hlt
                        · exact Or.inr ⟨heq, halen⟩
                        · exact Or.inl hlt
                      have hrec := rec q hrel
                      have hcontent : wittWordContent (a ++ z) =
                          wittWordContent (u ++ v) := by
                        calc
                          wittWordContent (a ++ z) = wittWordContent (a ++ (b ++ v)) :=
                            wittContent_append_replace hzcontent
                          _ = wittWordContent (u ++ v) := by rw [huab, List.append_assoc]
                      rw [hcontent] at hrec
                      exact wittLyndonSpanFrom_mono K hle hrec
                  · simp
                  · exact by
                      intro x y _ _ hx hy
                      simpa only [lie_add] using Submodule.add_mem _ hx hy
                  · exact by
                      intro c x _ hx
                      simpa only [lie_smul] using Submodule.smul_mem _ c hx
                have hterm2 :
                    ⁅wittLyndonBracket K b hb,
                      ⁅wittLyndonBracket K a ha, wittLyndonBracket K v hv⁆⁆ ∈
                      wittLyndonSpanFrom K (wittWordContent (u ++ v)) (u ++ v) := by
                  change ⁅wittLyndonBracket K a ha, wittLyndonBracket K v hv⁆ ∈
                    Submodule.span K {x | ∃ (w : List (Fin r)) (hw : IsLyndonWord w),
                      wittWordContent w = wittWordContent (a ++ v) ∧ a ++ v ≤ w ∧
                        x = wittLyndonBracket K w hw} at havsp
                  refine Submodule.span_induction (p := fun x _ =>
                    ⁅wittLyndonBracket K b hb, x⁆ ∈
                      wittLyndonSpanFrom K (wittWordContent (u ++ v)) (u ++ v))
                    ?_ ?_ ?_ ?_ havsp
                  · exact by
                      intro x hx
                      rcases hx with ⟨z, hz, hzcontent, havz, rfl⟩
                      have hzlen : z.length = (a ++ v).length :=
                        wittWordContent_eq_length_eq hzcontent
                      by_cases hbz : b = z
                      · subst z
                        simp
                      · rcases lt_or_gt_of_ne hbz with hbz | hzb
                        · have hbzlen : b.length + z.length = n := by
                            have hul := congr_arg List.length huab
                            simp only [List.length_append] at hul hzlen ⊢
                            omega
                          let q : WittLyndonPair r n := ⟨(b, z), hb, hz, hbz, hbzlen⟩
                          have habSwap := wittLyndon_append_lt_swap ha hb hab
                          have hfirst : (a ++ b) ++ v < (b ++ a) ++ v :=
                            wittAppend_right_lt_of_length_eq habSwap (by
                              simp only [List.length_append]
                              exact Nat.add_comm _ _) v
                          have htail : b ++ (a ++ v) ≤ b ++ z :=
                            wittAppend_le_append_of_le_of_le le_rfl rfl havz
                          have hlt : u ++ v < b ++ z := by
                            calc
                              u ++ v = (a ++ b) ++ v := by rw [huab]
                              _ < (b ++ a) ++ v := hfirst
                              _ = b ++ (a ++ v) := by rw [List.append_assoc]
                              _ ≤ b ++ z := htail
                          have hrel : WittLyndonPairRel q p := Or.inl hlt
                          have hrec := rec q hrel
                          have hcontent : wittWordContent (b ++ z) =
                              wittWordContent (u ++ v) := by
                            rw [huab]
                            simp only [wittWordContent_append]
                            funext i
                            have hzi := congr_fun hzcontent i
                            simp only [wittWordContent_append] at hzi
                            omega
                          rw [hcontent] at hrec
                          exact wittLyndonSpanFrom_mono K hlt.le hrec
                        · have hzbLen : z.length + b.length = n := by
                            have hul := congr_arg List.length huab
                            simp only [List.length_append] at hul hzlen ⊢
                            omega
                          let q : WittLyndonPair r n := ⟨(z, b), hz, hb, hzb, hzbLen⟩
                          have hbvSwap := wittLyndon_append_lt_swap hb hv hbv
                          have hprefix : a ++ (b ++ v) < a ++ (v ++ b) :=
                            (wittAppend_left_lt_iff a (b ++ v) (v ++ b)).mpr hbvSwap
                          have htail : (a ++ v) ++ b ≤ z ++ b :=
                            wittAppend_le_append_of_le_of_le havz hzlen.symm le_rfl
                          have hlt : u ++ v < z ++ b := by
                            calc
                              u ++ v = a ++ (b ++ v) := by rw [huab, List.append_assoc]
                              _ < a ++ (v ++ b) := hprefix
                              _ = (a ++ v) ++ b := by rw [List.append_assoc]
                              _ ≤ z ++ b := htail
                          have hrel : WittLyndonPairRel q p := Or.inl hlt
                          have hrec := rec q hrel
                          have hcontent : wittWordContent (z ++ b) =
                              wittWordContent (u ++ v) := by
                            rw [huab]
                            simp only [wittWordContent_append]
                            funext i
                            have hzi := congr_fun hzcontent i
                            simp only [wittWordContent_append] at hzi
                            omega
                          rw [hcontent] at hrec
                          have hmem := wittLyndonSpanFrom_mono K hlt.le hrec
                          simpa only [lie_skew] using Submodule.neg_mem _ hmem
                  · simp
                  · exact by
                      intro x y _ _ hx hy
                      simpa only [lie_add] using Submodule.add_mem _ hx hy
                  · exact by
                      intro c x _ hx
                      simpa only [lie_smul] using Submodule.smul_mem _ c hx
                rw [hPu, lie_lie]
                exact Submodule.sub_mem _ hterm1 hterm2
      exact hall p0

theorem wittBracket_mem_lyndonSpan (K : Type) [Field K] {r : ℕ}
    {u v : List (Fin r)} (hu : IsLyndonWord u) (hv : IsLyndonWord v) :
    ⁅wittLyndonBracket K u hu, wittLyndonBracket K v hv⁆ ∈
      wittLyndonSpanFrom K (wittWordContent (u ++ v)) [] := by
  rcases lt_trichotomy u v with huv | huv | huv
  · exact wittLyndonSpanFrom_mono K (wittNil_le (u ++ v))
      (wittOrderedBracket_mem_spanFrom_aux K (u.length + v.length) u v hu hv huv rfl)
  · subst v
    simp
  · have hmem := wittOrderedBracket_mem_spanFrom_aux K (v.length + u.length)
      v u hv hu huv rfl
    rw [← wittContent_swap_append u v] at hmem
    have hmem' := wittLyndonSpanFrom_mono K (wittNil_le (v ++ u)) hmem
    simpa only [lie_skew] using Submodule.neg_mem _ hmem'

theorem wittLyndonSpan_lie_mem (K : Type) [Field K] {r : ℕ}
    {a b : Fin r → ℕ} {x y : FreeLieAlgebra K (Fin r)}
    (hx : x ∈ wittLyndonSpanFrom K a []) (hy : y ∈ wittLyndonSpanFrom K b []) :
    ⁅x, y⁆ ∈ wittLyndonSpanFrom K (fun i => a i + b i) [] := by
  refine LinearMap.BilinMap.apply_apply_mem_of_mem_span
    (wittLyndonSpanFrom K (fun i => a i + b i) [])
    {z | ∃ (w : List (Fin r)) (hw : IsLyndonWord w),
      wittWordContent w = a ∧ [] ≤ w ∧ z = wittLyndonBracket K w hw}
    {z | ∃ (w : List (Fin r)) (hw : IsLyndonWord w),
      wittWordContent w = b ∧ [] ≤ w ∧ z = wittLyndonBracket K w hw}
    (LieModule.toEnd K (FreeLieAlgebra K (Fin r))
      (FreeLieAlgebra K (Fin r))).toLinearMap ?_ x y hx hy
  rintro _ ⟨u, hu, hua, _, rfl⟩ _ ⟨v, hv, hvb, _, rfl⟩
  have hmem := wittBracket_mem_lyndonSpan K hu hv
  have hcontent : wittWordContent (u ++ v) = fun i => a i + b i := by
    rw [wittWordContent_append, hua, hvb]
  rw [hcontent] at hmem
  exact hmem

theorem wittMonomial_mem_lyndonSpan (K : Type) [Field K] {r : ℕ}
    {degree : Fin r → ℕ} {x : FreeLieAlgebra K (Fin r)}
    (hx : IsFreeLieMonomial K degree x) :
    x ∈ wittLyndonSpanFrom K degree [] := by
  induction hx with
  | gen i =>
      let hi : IsLyndonWord [i] :=
        (wittLyndon_iff_suffix [i]).mpr (wittSuffixLyndon_singleton i)
      have hmem := wittLyndonBracket_mem_spanFrom K hi
        (wittWordContent_singleton i) (wittNil_le [i])
      simpa [wittLyndonBracket] using hmem
  | bracket ha hb iha ihb =>
      exact wittLyndonSpan_lie_mem K iha ihb

theorem wittMultihomogeneousComponent_eq_span (K : Type) [Field K] {r : ℕ}
    (degree : Fin r → ℕ) :
    freeLieMultihomogeneousComponent K degree =
      Submodule.span K (Set.range (wittLyndonFamily K degree)) := by
  rw [← wittLyndonSpan_eq_span_range K degree]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro x hx
    exact wittMonomial_mem_lyndonSpan K hx
  · apply Submodule.span_le.mpr
    rintro _ ⟨w, hw, hdegree, _, rfl⟩
    apply Submodule.subset_span
    rw [← hdegree]
    exact wittLyndonBracket_isMonomial K w hw

/-- Witt's formula for the dimension of a multihomogeneous component of a free Lie algebra. -/
theorem finrank_freeLieMultihomogeneousComponent
    (K : Type) [Field K] {r : ℕ} (degree : Fin r → ℕ)
    (hdegree : 0 < ∑ i, degree i) :
    (Module.finrank K (freeLieMultihomogeneousComponent K degree) : ℚ) =
      wittMultigradedValue degree := by
  rw [wittMultihomogeneousComponent_eq_span,
    finrank_span_eq_card (wittLyndonFamily_linearIndependent K degree)]
  exact card_lyndonWordsOfContent_eq_wittMultigradedValue degree hdegree

end MetaMathlibExt
