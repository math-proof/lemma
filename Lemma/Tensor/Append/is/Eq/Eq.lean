import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.DataAppend.as.AppendDataS
import Lemma.Tensor.DataAppend.as.FlattenMap₂_CastS_SplitAtData
import Lemma.Bool.SEq.is.Eq
import Lemma.Bool.SEq.of.SEq.SEq
import Lemma.List.Eq.of.Append.Length
import Lemma.Vector.Eq.is.ToList
import Lemma.Vector.Eq.is.All_EqGetS
import Lemma.Vector.Eq.of.Flatten
import Lemma.Vector.EqFlattenSplitAt
import Lemma.Vector.GetMap₂.eq.BFnGetS
open Tensor Bool Vector List


/--
| attributes | lemma |
| :---: | :---: |
| main | Tensor.Append.is.Eq.Eq |
| comm | Tensor.Eq.Eq.is.Append |
| mp | Tensor.Eq.Eq.of.Append |
| mpr | Tensor.Append.of.Eq.Eq |
-/
@[main, comm, mp, mpr]
private lemma main
  {A C : Tensor α (n :: s)}
  {B D : Tensor α (m :: s)} :
-- imply
  A ++ B = C ++ D ↔ A = C ∧ B = D := by
-- proof
  constructor
  ·
    intro h
    have hd : (A ++ B).data = (C ++ D).data := EqDataS.of.Eq h
    have hAB := DataAppend.as.AppendDataS A B
    have hCD := DataAppend.as.AppendDataS C D
    have happ : A.data ++ B.data ≃ C.data ++ D.data :=
      hAB.symm.trans ((SEq.of.Eq hd).trans hCD)
    have heq : A.data ++ B.data = C.data ++ D.data := Eq.of.SEq happ
    have hval : A.data.toList ++ B.data.toList = C.data.toList ++ D.data.toList := by
      rw [← List.Vector.toList_append, ← List.Vector.toList_append, heq]
    have hlen : A.data.toList.length = C.data.toList.length := by
      simp [List.Vector.toList]
    constructor
    ·
      apply Eq.of.EqDataS
      exact Eq.of.ToList (Eq.of.Append.Length hlen hval)
    ·
      apply Eq.of.EqDataS
      exact Eq.of.ToList (Eq.of.Append.Length.drop hlen hval)
  ·
    intro ⟨h₀, h₁⟩
    rw [h₀, h₁]


@[main, comm, mp, mpr]
private lemma batch
  {A C : Tensor α (batch_size ++ n :: s)}
  {B D : Tensor α (batch_size ++ m :: s)} :
-- imply
  A ++ B = C ++ D ↔ A = C ∧ B = D := by
-- proof
  constructor
  ·
    intro h
    have hd : (A ++ B).data = (C ++ D).data := EqDataS.of.Eq h
    let a : List.Vector (List.Vector α (n * s.prod)) batch_size.prod :=
      cast (by simp) (A.data.splitAt batch_size.length)
    let b : List.Vector (List.Vector α (m * s.prod)) batch_size.prod :=
      cast (by simp) (B.data.splitAt batch_size.length)
    let c : List.Vector (List.Vector α (n * s.prod)) batch_size.prod :=
      cast (by simp) (C.data.splitAt batch_size.length)
    let d : List.Vector (List.Vector α (m * s.prod)) batch_size.prod :=
      cast (by simp) (D.data.splitAt batch_size.length)
    have hAB : (A ++ B).data ≃ (List.Vector.map₂ HAppend.hAppend a b).flatten := by
      simpa [a, b] using DataAppend.as.FlattenMap₂_CastS_SplitAtData A B
    have hCD : (C ++ D).data ≃ (List.Vector.map₂ HAppend.hAppend c d).flatten := by
      simpa [c, d] using DataAppend.as.FlattenMap₂_CastS_SplitAtData C D
    have hflat : (List.Vector.map₂ HAppend.hAppend a b).flatten = (List.Vector.map₂ HAppend.hAppend c d).flatten := by
      apply Eq.of.SEq
      exact hAB.symm.trans ((SEq.of.Eq hd).trans hCD)
    have hmap : List.Vector.map₂ HAppend.hAppend a b = List.Vector.map₂ HAppend.hAppend c d :=
      Eq.of.Flatten hflat
    have ha : a = c := by
      apply Eq.of.All_EqGetS
      intro i
      have hi := GetMap₂.eq.BFnGetS (f := HAppend.hAppend) a b i
      have hj := GetMap₂.eq.BFnGetS (f := HAppend.hAppend) c d i
      have happ : a[i] ++ b[i] = c[i] ++ d[i] := by
        rw [← hi, ← hj, hmap]
      have hval : a[i].toList ++ b[i].toList = c[i].toList ++ d[i].toList := by
        rw [← List.Vector.toList_append, ← List.Vector.toList_append, happ]
      have hlen : a[i].toList.length = c[i].toList.length := by
        simp [List.Vector.toList]
      exact Eq.of.ToList (Eq.of.Append.Length hlen hval)
    have hb : b = d := by
      apply Eq.of.All_EqGetS
      intro i
      have hi := GetMap₂.eq.BFnGetS (f := HAppend.hAppend) a b i
      have hj := GetMap₂.eq.BFnGetS (f := HAppend.hAppend) c d i
      have happ : a[i] ++ b[i] = c[i] ++ d[i] := by
        rw [← hi, ← hj, hmap]
      have hval : a[i].toList ++ b[i].toList = c[i].toList ++ d[i].toList := by
        rw [← List.Vector.toList_append, ← List.Vector.toList_append, happ]
      have hlen : a[i].toList.length = c[i].toList.length := by
        simp [List.Vector.toList]
      exact Eq.of.ToList (Eq.of.Append.Length.drop hlen hval)
    have hsplitA : A.data.splitAt batch_size.length = C.data.splitAt batch_size.length := by
      have ha' := ha
      simp [a, c] at ha'
      exact (cast_inj (by simp)).1 ha'
    have hsplitB : B.data.splitAt batch_size.length = D.data.splitAt batch_size.length := by
      have hb' := hb
      simp [b, d] at hb'
      exact (cast_inj (by simp)).1 hb'
    constructor
    ·
      apply Eq.of.EqDataS
      apply Eq.of.SEq
      have hflatAC : (A.data.splitAt batch_size.length).flatten = (C.data.splitAt batch_size.length).flatten :=
        congrArg List.Vector.flatten hsplitA
      exact (EqFlattenSplitAt A.data batch_size.length).symm.trans
        ((SEq.of.Eq hflatAC).trans (EqFlattenSplitAt C.data batch_size.length))
    ·
      apply Eq.of.EqDataS
      apply Eq.of.SEq
      have hflatBD : (B.data.splitAt batch_size.length).flatten = (D.data.splitAt batch_size.length).flatten :=
        congrArg List.Vector.flatten hsplitB
      exact (EqFlattenSplitAt B.data batch_size.length).symm.trans
        ((SEq.of.Eq hflatBD).trans (EqFlattenSplitAt D.data batch_size.length))
  ·
    intro ⟨h₀, h₁⟩
    rw [h₀, h₁]


-- created on 2020-08-28
-- updated on 2026-09-09
