/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOnePolynomialSemantics.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneRawGenerated
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneLayerCode.Part2
import Std.Data.TreeMap.Lemmas
import Std.Data.DTreeMap.Internal.Lemmas
import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOnePolynomialSemantics
open Finset
open Std
open scoped Std.DTreeMap.Internal.Impl


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

theorem toList_alter_perm (m : BiTermMap) (k : Int × Int)
    (f : Option Int -> Option Int) :
    (m.alter k f).toList.Perm
      ((Std.Internal.List.Const.alterKey k f
        m.inner.inner.toListModel).map fun e => (e.1, e.2)) := by
  letI : Ord (Int × Int) := ⟨biExponentCompare⟩
  letI : TransOrd (Int × Int) :=
    inferInstanceAs (TransCmp biExponentCompare)
  letI : LawfulEqOrd (Int × Int) :=
    inferInstanceAs (LawfulEqCmp biExponentCompare)
  letI : LawfulBEqOrd (Int × Int) := by infer_instance
  have h := Std.DTreeMap.Internal.Impl.Const.toListModel_alter
      (t := m.inner.inner) (a := k) (f := f)
      m.inner.wf.balanced m.inner.wf.ordered
  have hm := h.map (fun e => (e.1, e.2))
  simpa only [TreeMap.alter, TreeMap.toList, DTreeMap.Const.alter,
    DTreeMap.Const.toList,
    Std.DTreeMap.Internal.Impl.Const.toList_eq_toListModel_map,
    List.map_map, Function.comp_apply] using hm

theorem sum_modelEntryEval_alterKey_addCoefficientOption
    (X Y : Real) (k : Int × Int) (d : Int)
    (l : List ((k : Int × Int) × (fun _ => Int) k))
    (hl : Std.Internal.List.DistinctKeys l) :
    ((Std.Internal.List.Const.alterKey k (addCoefficientOption d) l).map
        (modelEntryEval X Y)).sum =
      (l.map (modelEntryEval X Y)).sum +
        (d : Real) * X ^ k.1 * Y ^ k.2 := by
  induction l with
  | nil =>
      by_cases hd : d = 0
      · simp [Std.Internal.List.Const.alterKey_nil,
          addCoefficientOption, hd]
      · simp [Std.Internal.List.Const.alterKey_nil,
          addCoefficientOption, hd, modelEntryEval]
  | cons e l ih =>
      rcases e with ⟨ek, ec⟩
      rw [Std.Internal.List.distinctKeys_cons_iff] at hl
      have hp := Std.Internal.List.Const.alterKey_cons_perm
        (k := k) (f := addCoefficientOption d) (k' := ek)
        (v' := ec) (l := l)
      have hs := (hp.map (modelEntryEval X Y)).sum_eq
      rw [hs]
      by_cases hek : ek == k
      · simp only [hek, ↓reduceIte]
        have heq : ek = k := eq_of_beq hek
        subst ek
        by_cases hz : ec + d = 0
        · simp only [addCoefficientOption, hz, ↓reduceIte, List.map,
            List.sum_cons, modelEntryEval]
          have hzR : (ec : Real) + (d : Real) = 0 := by
            exact_mod_cast hz
          symm
          calc
            (ec : Real) * X ^ k.1 * Y ^ k.2 +
                (l.map (modelEntryEval X Y)).sum +
                (d : Real) * X ^ k.1 * Y ^ k.2 =
              (l.map (modelEntryEval X Y)).sum +
                ((ec : Real) + (d : Real)) *
                  (X ^ k.1 * Y ^ k.2) := by ring
            _ = (l.map (modelEntryEval X Y)).sum := by rw [hzR]; ring
        · simp only [addCoefficientOption, hz, ↓reduceIte, List.map,
            List.sum_cons, modelEntryEval]
          push_cast
          ring
      · simp only [hek, Bool.false_eq_true, ↓reduceIte, List.map,
          List.sum_cons, modelEntryEval]
        rw [ih hl.1]
        ring


theorem termMapEval_addTermToMap
    (X Y : Real) (m : BiTermMap) (t : BiTerm) :
    termMapEval X Y (addTermToMap m t) =
      termMapEval X Y m + t.eval X Y := by
  letI : Ord (Int × Int) := ⟨biExponentCompare⟩
  letI : TransOrd (Int × Int) :=
    inferInstanceAs (TransCmp biExponentCompare)
  letI : LawfulEqOrd (Int × Int) :=
    inferInstanceAs (LawfulEqCmp biExponentCompare)
  letI : LawfulBEqOrd (Int × Int) := by infer_instance
  unfold termMapEval addTermToMap BiTerm.eval
  have hp := toList_alter_perm m (t.ex, t.ey)
    (addCoefficientOption t.coeff)
  rw [(hp.map fun e =>
    (e.2 : Real) * X ^ e.1.1 * Y ^ e.1.2).sum_eq]
  simpa only [TreeMap.toList, DTreeMap.Const.toList,
    Std.DTreeMap.Internal.Impl.Const.toList_eq_toListModel_map,
    List.map_map, Function.comp_apply, modelEntryEval] using
    sum_modelEntryEval_alterKey_addCoefficientOption X Y (t.ex, t.ey)
      t.coeff m.inner.inner.toListModel m.inner.wf.ordered.distinctKeys

theorem termMapEval_foldl_addTermToMap
    (X Y : Real) (m : BiTermMap) (ts : List BiTerm) :
    termMapEval X Y (ts.foldl addTermToMap m) =
      termMapEval X Y m + (ts.map (BiTerm.eval X Y)).sum := by
  induction ts generalizing m with
  | nil => simp
  | cons t ts ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih, termMapEval_addTermToMap]
      ring

theorem BiPoly.eval_ofTerms (X Y : Real) (ts : List BiTerm) :
    BiPoly.eval X Y (BiPoly.ofTerms ts) =
      (ts.map (BiTerm.eval X Y)).sum := by
  rw [BiPoly.ofTerms]
  unfold BiPoly.eval
  simp only [List.map_map]
  change termMapEval X Y
      (ts.foldl addTermToMap (TreeMap.empty : BiTermMap)) = _
  rw [termMapEval_foldl_addTermToMap]
  have hempty : termMapEval X Y (TreeMap.empty : BiTermMap) = 0 := by
    unfold termMapEval TreeMap.empty TreeMap.toList DTreeMap.Const.toList
    rfl
  rw [hempty, zero_add]

@[simp] theorem BiPoly.eval_monomial (X Y : Real) (ex ey coeff : Int) :
    BiPoly.eval X Y (.monomial ex ey coeff) =
      (coeff : Real) * X ^ ex * Y ^ ey := by
  rw [BiPoly.monomial, BiPoly.eval_ofTerms]
  simp [BiTerm.eval]

@[simp] theorem BiPoly.eval_add (X Y : Real) (p q : BiPoly) :
    BiPoly.eval X Y (p + q) = p.eval X Y + q.eval X Y := by
  change BiPoly.eval X Y (BiPoly.add p q) = _
  rw [BiPoly.add, BiPoly.eval_ofTerms]
  simp [BiPoly.eval]

@[simp] theorem BiPoly.eval_neg (X Y : Real) (p : BiPoly) :
    BiPoly.eval X Y (-p) = -p.eval X Y := by
  change BiPoly.eval X Y (BiPoly.neg p) = _
  rw [BiPoly.neg, BiPoly.eval_ofTerms]
  unfold BiPoly.eval
  induction p.terms with
  | nil => simp
  | cons t ts ih =>
      simp only [List.map_map, List.map_cons, List.sum_cons,
        ] at ih ⊢
      unfold BiTerm.eval at ih ⊢
      push_cast
      rw [ih]
      ring

@[simp] theorem BiPoly.eval_sub (X Y : Real) (p q : BiPoly) :
    BiPoly.eval X Y (p - q) = p.eval X Y - q.eval X Y := by
  change BiPoly.eval X Y (BiPoly.sub p q) = _
  rw [BiPoly.sub]
  change BiPoly.eval X Y (p + (-q)) = _
  rw [BiPoly.eval_add, BiPoly.eval_neg]
  rfl

theorem sum_termProduct_right
    (X Y : Real) (hX : X ≠ 0) (hY : Y ≠ 0)
    (s : BiTerm) (ts : List BiTerm) :
    (((ts.map fun t =>
        { ex := s.ex + t.ex, ey := s.ey + t.ey,
          coeff := s.coeff * t.coeff }).map (BiTerm.eval X Y)).sum) =
      s.eval X Y * (ts.map (BiTerm.eval X Y)).sum := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
      simp only [List.map_cons, List.sum_cons] at ih ⊢
      rw [ih]
      unfold BiTerm.eval
      simp only [Int.cast_mul, zpow_add₀ hX, zpow_add₀ hY]
      ring

theorem sum_termProducts
    (X Y : Real) (hX : X ≠ 0) (hY : Y ≠ 0)
    (ss ts : List BiTerm) :
    ((ss.flatMap fun s => ts.map fun t =>
        { ex := s.ex + t.ex, ey := s.ey + t.ey,
          coeff := s.coeff * t.coeff }).map (BiTerm.eval X Y)).sum =
      (ss.map (BiTerm.eval X Y)).sum *
        (ts.map (BiTerm.eval X Y)).sum := by
  induction ss with
  | nil => simp
  | cons s ss ih =>
      simp only [List.flatMap_cons, List.map_append, List.sum_append,
        List.map_cons, List.sum_cons, ih]
      rw [sum_termProduct_right X Y hX hY]
      ring

@[simp] theorem BiPoly.eval_mul (X Y : Real) (hX : X ≠ 0) (hY : Y ≠ 0)
    (p q : BiPoly) :
    BiPoly.eval X Y (p * q) = p.eval X Y * q.eval X Y := by
  change BiPoly.eval X Y (BiPoly.mul p q) = _
  rw [BiPoly.mul, BiPoly.eval_ofTerms]
  exact sum_termProducts X Y hX hY p.terms q.terms

theorem BiPoly.eval_mapExponent (X Y : Real)
    (f : Int -> Int -> Int × Int) (p : BiPoly) :
    (p.mapExponent f).eval X Y =
      (p.terms.map fun t =>
        (t.coeff : Real) * X ^ (f t.ex t.ey).1 *
          Y ^ (f t.ex t.ey).2).sum := by
  rw [BiPoly.mapExponent, BiPoly.eval_ofTerms]
  simp only [List.map_map]
  congr 1

theorem BiPoly.eval_flipY (X Y : Real) (p : BiPoly) :
    (p.mapExponent fun ex ey => (ex, -ey)).eval X Y =
      p.eval X Y⁻¹ := by
  rw [BiPoly.eval_mapExponent]
  unfold BiPoly.eval
  congr 1
  apply List.map_congr_left
  intro t ht
  unfold BiTerm.eval
  rw [inv_zpow]
  rw [zpow_neg]

theorem BiPoly.eval_scaleObservable (X Y : Real) (p : BiPoly)
    (power : Nat) :
    (p.scaleObservable power).eval X Y =
      (p.terms.map fun t =>
        ((t.coeff * (2 * t.ey - 9) ^ power : Int) : Real) *
          X ^ t.ex * Y ^ t.ey).sum := by
  rw [BiPoly.scaleObservable, BiPoly.eval_ofTerms]
  simp only [List.map_map]
  congr 1

end StatMech.FrontierA.NOneSymmetricMeanCertificate
