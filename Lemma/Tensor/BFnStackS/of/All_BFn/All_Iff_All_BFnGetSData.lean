import Lemma.Fin.Any_Eq_AddMul.of.Lt_Mul
import Lemma.List.Prod.eq.Foldr
import Lemma.Tensor.DataOfVector.eq.FlattenMapData
import Lemma.Vector.EqGetRange
import Lemma.Vector.GetFlatten_AddMul.eq.Get
import sympy.tensor.stack
open Fin List Tensor Vector


@[main]
private lemma main
  {α : Type u}
  {R : ∀ {m : List ℕ}, Tensor α m → Tensor α m → Prop}
  {R₀ : α → α → Prop}
  {X Y : Fin n → Tensor α s}
-- given
  (hDataS : ∀ {m : List ℕ} (A B : Tensor α m), R A B ↔ ∀ j : Fin m.prod, R₀ A.data[j] B.data[j])
  (h : ∀ i : Fin n, R (X i) (Y i)) :
-- imply
  R ([i < n] X i) ([i < n] Y i) := by
-- proof
  unfold Stack
  rw [hDataS]
  intro k
  rw [DataOfVector.eq.FlattenMapData, DataOfVector.eq.FlattenMapData]
  let h₀ := fun i j => (hDataS (X i) (Y i)).mp (h i) j
  let rangeX := (List.Vector.range n).map X
  let rangeY := (List.Vector.range n).map Y
  let rowsX := rangeX.map data
  let rowsY := rangeY.map data
  have hprod : (n :: s).prod = n * s.prod := by simp
  obtain ⟨i, j, hij⟩ := Any_Eq_AddMul.of.Lt_Mul (Nat.lt_of_lt_of_eq k.isLt hprod.symm)
  have hk_lt : i * s.prod + j < n * s.prod := calc
    i * s.prod + j = k.val := by simp [← hij, Prod.eq.Foldr]
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
  have hk_eq : k' = ⟨i * s.prod + j, hk_lt⟩ := Fin.ext (by simp [Prod.eq.Foldr]; grind)
  let j' : Fin s.prod := Fin.cast (Prod.eq.Foldr s).symm j
  have hj : j = Fin.cast (Prod.eq.Foldr s) j' := Fin.ext (by simp [j'])
  have hmid : R₀ rowsX[i][j] rowsY[i][j] := by
    rw [hrowsX', hrowsY', hj]
    exact h₀ i j'
  have hR : R₀ rowsX.flatten[k'] rowsY.flatten[k'] := by
    have h₁ : rowsX.flatten[k'] = rowsX[i][j] := calc
      rowsX.flatten[k'] = rowsX.flatten[i * s.prod + j]'hk_lt := by simp [hk_eq]
      _ = rowsX[i][j] := hflatX
    have h₂ : rowsY.flatten[k'] = rowsY[i][j] := calc
      rowsY.flatten[k'] = rowsY.flatten[i * s.prod + j]'hk_lt := by simp [hk_eq]
      _ = rowsY[i][j] := hflatY
    exact h₂.symm ▸ h₁.symm ▸ hmid
  have hflat_eqX : (((List.Vector.range n).map fun i => X i).map data).flatten[k] = rowsX.flatten[k'] := by
    dsimp [rowsX, rangeX, k']
    simp [GetElem.getElem]
    rfl
  have hflat_eqY : (((List.Vector.range n).map fun i => Y i).map data).flatten[k] = rowsY.flatten[k'] := by
    dsimp [rowsY, rangeY, k']
    simp [GetElem.getElem]
    rfl
  exact hflat_eqY ▸ hflat_eqX ▸ hR


-- created on 2026-07-27
