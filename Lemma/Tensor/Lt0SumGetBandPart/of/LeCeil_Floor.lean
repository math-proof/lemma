import Lemma.Finset.GtSumS.of.Any_Gt.All_Ge
import Lemma.Rat.LeCeil_Floor.is.Any_And_Dvd_AddSub
import Lemma.Tensor.BandPart.eq.Stack_BoolAnd_Dvd
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.EqData0'0
import Lemma.Tensor.EqData1'1
import Lemma.Tensor.EqGetStack
import Lemma.Tensor.GetData.eq.GetDataGet.of.Lt
import Lemma.Tensor.Le.is.LeDataS
import Lemma.Tensor.Ge_0.is.All_Le0GetData
import Lemma.Tensor.Le0Stack.of.All_Ge_0
import Lemma.Tensor.Sum.eq.MkListSumData
import Lemma.Vector.EqGet1_1
import Lemma.Vector.Sum.eq.Sum_Get
import sympy.sets.sets
open Finset Rat Tensor Vector


@[main]
private lemma main
  [AddCommMonoidWithOne α]
  [PartialOrder α]
  [ZeroLEOneClass α]
  [IsOrderedCancelAddMonoid α]
  [NeZero (1 : α)]
  [NeZero n]
  [NeZero (d : ℕ)]
-- given
  (m l u : ℕ)
  (i : Fin m)
  (h_icc : ⌈((↑(i - l) : ℤ) - ((i : ℤ) - l)) / (d : ℚ)⌉ ≤ ⌊((↑((n - 1) ⊓ (i + u)) : ℤ) - ((i : ℤ) - l)) / (d : ℚ)⌋) :
-- imply
  (((1 : Tensor α [m, n]).band_part l u d).get i).sum > 0 := by
-- proof
  let band_row : Fin m → Tensor α [n] := fun i => [j < n] (((j - i : ℤ) ∈ Set.Icc (-l : ℤ) u ∧ (d : ℤ) ∣ (j - i : ℤ) + l) : Bool)
  suffices h : (band_row i).sum > 0 by rwa [BandPart.eq.Stack_BoolAnd_Dvd m n l u d, EqGetStack.fn.fin band_row i]
  let row := band_row i
  have ⟨j, hband, hdvd⟩ := Any_And_Dvd_AddSub.of.LeCeil_Floor (l := l) (u := u) (i := ↑i) h_icc
  have hprod : [n].prod = n := by simp
  let hj : Fin [n].prod := Fin.cast hprod.symm j
  have h_row_ge : row ≥ 0 := by
    dsimp [row, band_row]
    apply Le0Stack.of.All_Ge_0
    intro j'
    refine ge_iff_le.mpr ?_
    apply Le.of.LeDataS
    intro k
    if hmem : (j' - i : ℤ) ∈ Set.Icc (-l : ℤ) u then
      if hdvd' : (d : ℤ) ∣ (j' - i : ℤ) + l then
        obtain ⟨h_l', h_u'⟩ := Set.mem_Icc.mp hmem
        have h1' : (↑i : ℤ) ≤ ↑j' + l := by linarith
        have h2' : (↑j' : ℤ) ≤ ↑u + ↑i := by linarith
        fin_cases k
        simp [EqData0'0, h1', h2', hdvd', EqData1'1]
        exact zero_le_one
      else
        fin_cases k
        simp [EqData0'0, decide_eq_false_iff_not.mpr hdvd', Bool.and_false, Bool.toNat_false, Nat.cast_zero]
    else
      rw [Set.mem_Icc, not_and_or] at hmem
      if hlt : (-l : ℤ) ≤ j' - i then
        have h2' : ¬((j' - i : ℤ) ≤ u) := by
          obtain h | h := hmem <;>
            aesop
        have h2'' : ¬(↑j' : ℤ) ≤ ↑u + ↑i := by linarith
        fin_cases k
        simp [EqData0'0, decide_eq_false h2'', Bool.and_false, Bool.toNat_false, Nat.cast_zero]
      else
        have h1'' : ¬(↑i : ℤ) ≤ ↑j' + l := by linarith
        fin_cases k
        simp [EqData0'0, decide_eq_false h1'', Bool.false_and, Bool.toNat_false, Nat.cast_zero]
  let band_entry : Fin n → Tensor α [] := fun j' => ↑(decide ((j' - i : ℤ) ∈ Set.Icc (-l : ℤ) u ∧ (d : ℤ) ∣ (j' - i : ℤ) + l)).toNat
  have hstack : row[j] = band_entry j := by
    dsimp [row, band_row]
    exact EqGetStack.fn.fin band_entry j
  have h_tensor : row[j] = (1 : Tensor α []) := by
    rw [hstack]
    dsimp [band_entry]
    rw [decide_eq_true (And.intro hband hdvd), Bool.toNat_true]
    apply Eq.of.EqDataS
    simp [EqData1'1]
  have h_gt : 0 < row.data[hj] := by
    have hdata := GetData.eq.GetDataGet.of.Lt.fin (α := α) (n := n) (i := j) (h_i := j.isLt) row
    have ht : row[j].data[0] = (1 : α) := calc
      _ = ((1 : Tensor α [])).data[0] := congr_arg (fun t => t.data[0]) h_tensor
      _ = 1 := by
        rw [EqData1'1, GetElem.getElem]
        exact EqGet1_1.fin (0 : Fin 1)
    have hpos : (0 : α) < row[j].data[0] := ht ▸ (zero_lt_one : (0 : α) < (1 : α))
    calc
      _ < row[j].data[0] := hpos
      _ = row.data[j] := by simpa [GetElem.getElem] using hdata.symm
      _ = row.data[hj] := by simp [hj, GetElem.getElem]
  have h_data : row.data.sum > 0 := by
    rw [Sum.eq.Sum_Get (n := [n].prod)]
    have hpos := GtSumS.of.Any_Gt.All_Ge
      (x := row.data.get)
      (y := fun _ => 0)
      (fun k _ => All_Le0GetData.of.Ge_0 h_row_ge k)
      ⟨hj, Finset.mem_univ hj, h_gt⟩
    simp [Finset.sum_const_zero] at hpos
    simpa
  rw [Sum.eq.MkListSumData (X := row)]
  intro k
  fin_cases k
  assumption


-- created on 2026-07-28
