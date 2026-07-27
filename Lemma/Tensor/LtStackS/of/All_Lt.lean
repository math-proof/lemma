import Lemma.Fin.Any_Eq_AddMul.of.Lt_Mul
import Lemma.List.Prod.eq.Foldr
import Lemma.Nat.AddMul.lt.Mul
import Lemma.Tensor.DataFromVector.eq.FlattenMapData
import Lemma.Tensor.Lt.is.LtDataS
import Lemma.Vector.EqGetRange
import Lemma.Vector.GetFlatten_AddMul.eq.Get
import sympy.tensor.stack
open Tensor Vector Nat


@[main]
private lemma flatten_map_data
  {α : Type u}
  (R : α → α → Prop)
  {X Y : Fin n → Tensor α s}
  (h : ∀ i : Fin n, ∀ j : Fin s.prod, R (X i).data[j] (Y i).data[j])
  (k : Fin (n :: s).prod) :
  R
    (((List.Vector.range n).map fun i => X i).map data).flatten[k]
    (((List.Vector.range n).map fun i => Y i).map data).flatten[k] := by
  let rangeX := (List.Vector.range n).map (fun i => X i)
  let rangeY := (List.Vector.range n).map (fun i => Y i)
  let rowsX := rangeX.map data
  let rowsY := rangeY.map data
  have hprod : (n :: s).prod = n * s.prod := by simp
  obtain ⟨i, j, hij⟩ := Fin.Any_Eq_AddMul.of.Lt_Mul (Nat.lt_of_lt_of_eq k.isLt hprod.symm)
  have hk_lt : i * s.prod + j < n * s.prod := calc
    i * s.prod + j = k.val := by simp [← hij, List.Prod.eq.Foldr]
    _ < (n :: s).prod := k.isLt
    _ = n * s.prod := hprod
  have hflatX := GetFlatten_AddMul.eq.Get (v := rowsX) i j
  have hflatY := GetFlatten_AddMul.eq.Get (v := rowsY) i j
  have hrowsX' : rowsX[i] = (X i).data := by
    dsimp only [rowsX, rangeX]
    simp [GetElem.getElem, EqGetRange.fin]
  have hrowsY' : rowsY[i] = (Y i).data := by
    dsimp only [rowsY, rangeY]
    simp [GetElem.getElem, EqGetRange.fin]
  let k' : Fin (n * s.prod) := Fin.cast hprod k
  have hk_eq : k' = ⟨i * s.prod + j, hk_lt⟩ := Fin.ext (by simp [k', hij, List.Prod.eq.Foldr])
  let j' : Fin s.prod := Fin.cast (List.Prod.eq.Foldr s).symm j
  have hj : j = Fin.cast (List.Prod.eq.Foldr s) j' := Fin.ext (by simp [j'])
  have hmid : R rowsX[i][j] rowsY[i][j] := by
    rw [hrowsX', hrowsY', hj]
    exact h i j'
  have hR : R rowsX.flatten[k'] rowsY.flatten[k'] := by
    have h₁ : rowsX.flatten[k'] = rowsX[i][j] := by
      calc
        rowsX.flatten[k'] = rowsX.flatten[i * s.prod + j]'hk_lt := by simp [hk_eq]
        _ = rowsX[i][j] := hflatX
    have h₂ : rowsY.flatten[k'] = rowsY[i][j] := by
      calc
        rowsY.flatten[k'] = rowsY.flatten[i * s.prod + j]'hk_lt := by simp [hk_eq]
        _ = rowsY[i][j] := hflatY
    exact h₂.symm ▸ h₁.symm ▸ hmid
  have hflat_eqX :
      (((List.Vector.range n).map fun i => X i).map data).flatten[k] = rowsX.flatten[k'] := by
    dsimp [rowsX, rangeX, k']
    simp [GetElem.getElem]
  have hflat_eqY :
      (((List.Vector.range n).map fun i => Y i).map data).flatten[k] = rowsY.flatten[k'] := by
    dsimp [rowsY, rangeY, k']
    simp [GetElem.getElem]
  rw [hflat_eqX, hflat_eqY]
  exact hR


@[main]
private lemma main
  [LT α]
  {X Y : Fin n → Tensor α s}
-- given
  (h : ∀ i : Fin n, X i < Y i) :
-- imply
  [i < n] X i < [i < n] Y i := by
-- proof
  unfold Stack
  apply Lt.of.LtDataS
  rw [DataFromVector.eq.FlattenMapData, DataFromVector.eq.FlattenMapData]
  simp only [LT.lt]
  intro k
  exact flatten_map_data (@LT.lt α _) (fun i j => by
    have hi := LtDataS.of.Lt (h i)
    simp only [LT.lt] at hi
    exact hi j) k


-- created on 2026-07-27
