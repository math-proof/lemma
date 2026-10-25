/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDenseIncidencePrimitiveBridge.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicReflectedTensorTent.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCenteredRadialPatch.Part12
import Def.StatisticalMechanics.Code.Universality.IsingFermionicTensorTentMorera.Part7


namespace StatMech.Universality

open Filter Set Topology

open scoped BigOperators

noncomputable section

theorem reflectedRadialAxisStaircasePathIntegral_eq_axisTwoEdge
    (f : Complex -> Complex) (mesh : Real)
    (n i0 j0 width height : Nat) :
    let p := isingReflectedCenteredRadialGridPosition
      mesh n (i0 + height) j0
    reflectedRadialAxisStaircasePathIntegral
        f mesh n i0 j0 width height =
      axisTwoEdgeStaircasePathIntegral
        f p.re p.im mesh width height := by
  let p := isingReflectedCenteredRadialGridPosition
    mesh n (i0 + height) j0
  let u : Complex := (mesh : Complex) / 2 * (1 - Complex.I)
  let v : Complex := (mesh : Complex) / 2 * (1 + Complex.I)
  have hbottomBase (k : Nat) :
      isingReflectedCenteredRadialGridPosition mesh n
          (i0 + height + k) (j0 + k) =
        (p.re + (k : Real) * mesh : Real) + p.im * Complex.I := by
    calc
      _ = p + (k : Real) * mesh := by
        simpa [p, Nat.add_assoc] using
          isingReflectedCenteredRadialGridPosition_diagonal_add
            mesh n (i0 + height) j0 k
      _ = _ := by apply Complex.ext <;> simp <;> ring
  have hbottomTurn (k : Nat) :
      isingReflectedCenteredRadialGridPosition mesh n
          (i0 + height + k + 1) (j0 + k) =
        ((p.re + (k : Real) * mesh : Real) + p.im * Complex.I) + u := by
    rw [show i0 + height + k + 1 = (i0 + height + k) + 1 by omega,
      isingReflectedCenteredRadialGridPosition_succ_i,
      hbottomBase]
  have hrightBase (k : Nat) (hk : k < height) :
      isingReflectedCenteredRadialGridPosition mesh n
          (i0 + width + (height - 1 - k) + 1) (j0 + width + k) =
        (p.re + (width : Real) * mesh : Real) +
          (p.im + (k : Real) * mesh : Real) * Complex.I := by
    have hk' : k ≤ height := by omega
    have hsub : height - 1 - k + 1 = height - k := by omega
    have hindex : i0 + width + (height - 1 - k) + 1 =
        (i0 + width) + (height - k) := by
      rw [Nat.add_assoc, hsub]
    calc
      _ = isingReflectedCenteredRadialGridPosition mesh n
          ((i0 + width) + (height - k)) ((j0 + width) + k) := by
        rw [hindex]
      _ = isingReflectedCenteredRadialGridPosition mesh n
          ((i0 + width) + height) (j0 + width) +
            ((k : Real) * mesh) * Complex.I :=
        isingReflectedCenteredRadialGridPosition_antidiagonal_add
          mesh n (i0 + width) (j0 + width) height k hk'
      _ = p + (width : Real) * mesh +
            ((k : Real) * mesh) * Complex.I := by
        rw [show i0 + width + height = i0 + height + width by omega]
        rw [show j0 + width = j0 + width by rfl]
        rw [show isingReflectedCenteredRadialGridPosition mesh n
            (i0 + height + width) (j0 + width) =
              p + (width : Real) * mesh by
          simpa [p, Nat.add_assoc] using
            isingReflectedCenteredRadialGridPosition_diagonal_add
              mesh n (i0 + height) j0 width]
      _ = _ := by apply Complex.ext <;> simp <;> ring
  have hrightTurn (k : Nat) (hk : k < height) :
      isingReflectedCenteredRadialGridPosition mesh n
          (i0 + width + (height - 1 - k) + 1)
          (j0 + width + k + 1) =
        ((p.re + (width : Real) * mesh : Real) +
          (p.im + (k : Real) * mesh : Real) * Complex.I) + v := by
    rw [show j0 + width + k + 1 = (j0 + width + k) + 1 by omega,
      isingReflectedCenteredRadialGridPosition_succ_j,
      hrightBase k hk]
  have htopBase (k : Nat) (hk : k < width) :
      isingReflectedCenteredRadialGridPosition mesh n
          (i0 + (width - 1 - k) + 1)
          (j0 + height + (width - 1 - k) + 1) =
        (p.re + (width : Real) * mesh - (k : Real) * mesh : Real) +
          (p.im + (height : Real) * mesh : Real) * Complex.I := by
    have hk' : k ≤ width := by omega
    have hsub : width - 1 - k + 1 = width - k := by omega
    have hi : i0 + (width - 1 - k) + 1 = i0 + (width - k) := by
      rw [Nat.add_assoc, hsub]
    have hj : j0 + height + (width - 1 - k) + 1 =
        (j0 + height) + (width - k) := by
      rw [Nat.add_assoc, hsub]
    calc
      _ = isingReflectedCenteredRadialGridPosition mesh n
          (i0 + (width - k)) ((j0 + height) + (width - k)) := by
        rw [hi, hj]
      _ = isingReflectedCenteredRadialGridPosition mesh n
          (i0 + width) ((j0 + height) + width) -
            (k : Real) * mesh :=
        isingReflectedCenteredRadialGridPosition_diagonal_sub
          mesh n i0 (j0 + height) width width k hk' hk'
      _ = isingReflectedCenteredRadialGridPosition mesh n
          i0 (j0 + height) + (width : Real) * mesh -
            (k : Real) * mesh := by
        rw [isingReflectedCenteredRadialGridPosition_diagonal_add]
      _ = p + ((height : Real) * mesh) * Complex.I +
            (width : Real) * mesh - (k : Real) * mesh := by
        rw [show isingReflectedCenteredRadialGridPosition mesh n
            i0 (j0 + height) =
              p + ((height : Real) * mesh) * Complex.I by
          simpa [p] using
            isingReflectedCenteredRadialGridPosition_antidiagonal_add
              mesh n i0 j0 height height (le_refl height)]
      _ = _ := by apply Complex.ext <;> simp <;> ring
  have htopTurn (k : Nat) (hk : k < width) :
      isingReflectedCenteredRadialGridPosition mesh n
          (i0 + (width - 1 - k))
          (j0 + height + (width - 1 - k) + 1) =
        ((p.re + (width : Real) * mesh - (k : Real) * mesh : Real) +
          (p.im + (height : Real) * mesh : Real) * Complex.I) - u := by
    have hs := isingReflectedCenteredRadialGridPosition_succ_i
      mesh n (i0 + (width - 1 - k))
        (j0 + height + (width - 1 - k) + 1)
    have hs' :
        isingReflectedCenteredRadialGridPosition mesh n
            (i0 + (width - 1 - k) + 1)
            (j0 + height + (width - 1 - k) + 1) =
          isingReflectedCenteredRadialGridPosition mesh n
              (i0 + (width - 1 - k))
              (j0 + height + (width - 1 - k) + 1) + u := by
      simpa [u] using hs
    rw [htopBase k hk] at hs'
    linear_combination -hs'
  have hleftBase (k : Nat) (hk : k < height) :
      isingReflectedCenteredRadialGridPosition mesh n
          (i0 + k) (j0 + (height - 1 - k) + 1) =
        p.re +
          (p.im + (height : Real) * mesh - (k : Real) * mesh : Real) *
            Complex.I := by
    have hk' : k ≤ height := by omega
    have hsub : height - 1 - k + 1 = height - k := by omega
    have hj : j0 + (height - 1 - k) + 1 = j0 + (height - k) := by
      rw [Nat.add_assoc, hsub]
    calc
      _ = isingReflectedCenteredRadialGridPosition mesh n
          (i0 + k) (j0 + (height - k)) := by rw [hj]
      _ = isingReflectedCenteredRadialGridPosition mesh n
          i0 (j0 + height) - ((k : Real) * mesh) * Complex.I :=
        isingReflectedCenteredRadialGridPosition_antidiagonal_sub
          mesh n i0 j0 height k hk'
      _ = p + ((height : Real) * mesh) * Complex.I -
            ((k : Real) * mesh) * Complex.I := by
        rw [show isingReflectedCenteredRadialGridPosition mesh n
            i0 (j0 + height) =
              p + ((height : Real) * mesh) * Complex.I by
          simpa [p] using
            isingReflectedCenteredRadialGridPosition_antidiagonal_add
              mesh n i0 j0 height height (le_refl height)]
      _ = _ := by apply Complex.ext <;> simp <;> ring
  have hleftTurn (k : Nat) (hk : k < height) :
      isingReflectedCenteredRadialGridPosition mesh n
          (i0 + k) (j0 + (height - 1 - k)) =
        (p.re +
          (p.im + (height : Real) * mesh - (k : Real) * mesh : Real) *
            Complex.I) - v := by
    have hs := isingReflectedCenteredRadialGridPosition_succ_j
      mesh n (i0 + k) (j0 + (height - 1 - k))
    have hs' :
        isingReflectedCenteredRadialGridPosition mesh n
            (i0 + k) (j0 + (height - 1 - k) + 1) =
          isingReflectedCenteredRadialGridPosition mesh n
              (i0 + k) (j0 + (height - 1 - k)) + v := by
      simpa [v] using hs
    rw [hleftBase k hk] at hs'
    linear_combination -hs'
  unfold reflectedRadialAxisStaircasePathIntegral
    axisTwoEdgeStaircasePathIntegral
  dsimp only
  congr 1
  · congr 1
    · congr 1
      · apply Finset.sum_congr rfl
        intro k _hk
        rw [hbottomBase k, hbottomTurn k]
      · apply Finset.sum_congr rfl
        intro k hk
        rw [hrightBase k (Finset.mem_range.mp hk),
          hrightTurn k (Finset.mem_range.mp hk)]
    · apply Finset.sum_congr rfl
      intro k hk
      rw [htopBase k (Finset.mem_range.mp hk),
        htopTurn k (Finset.mem_range.mp hk)]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [hleftBase k (Finset.mem_range.mp hk),
      hleftTurn k (Finset.mem_range.mp hk)]


theorem reflectedRadialAxisStaircaseBoundaryIntegral_eq_zero_of_cellCR
    (mesh : Real) (F : Nat -> Nat -> Complex)
    (i0 j0 width height : Nat)
    (hCR : ∀ a b, a < width + height -> b < width + height ->
      IsingCellCRAt F (i0 + a) (j0 + b)) :
    reflectedRadialAxisStaircaseBoundaryIntegral
      mesh F i0 j0 width height = 0 := by
  let H := reflectedRadialHorizontalEdgeIntegral mesh F
  let V := reflectedRadialVerticalEdgeIntegral mesh F
  let P : Nat -> Nat -> Complex := fun a b =>
    reflectedRadialDiscretePrimitive H V i0 j0 a b
  have hPi (a b : Nat) (ha : a < width + height)
      (hb : b ≤ width + height) :
      P (a + 1) b - P a b = H (i0 + a) (j0 + b) := by
    dsimp only [P, H, V]
    apply reflectedRadialDiscretePrimitive_succ_i_of_cellCR
    intro y hy
    exact hCR a y ha (lt_of_lt_of_le hy hb)
  have hPj (a b : Nat) :
      P a (b + 1) - P a b = V (i0 + a) (j0 + b) := by
    exact reflectedRadialDiscretePrimitive_succ_j H V i0 j0 a b
  let qb : Nat -> Complex := fun k => P (height + k) k
  let qr : Nat -> Complex := fun k => P (width + (height - k)) (width + k)
  let qt : Nat -> Complex := fun k => P (width - k) (height + (width - k))
  let ql : Nat -> Complex := fun k => P k (height - k)
  have hbottom (k : Nat) (hk : k < width) :
      H (i0 + height + k) (j0 + k) +
          V (i0 + height + k + 1) (j0 + k) =
        qb (k + 1) - qb k := by
    have hi := hPi (height + k) k (by omega) (by omega)
    have hj := hPj (height + k + 1) k
    dsimp only [qb]
    simp only [Nat.add_assoc]
    linear_combination -hi - hj
  have hright (k : Nat) (hk : k < height) :
      V (i0 + width + (height - 1 - k) + 1) (j0 + width + k) -
          H (i0 + width + (height - 1 - k)) (j0 + width + k + 1) =
        qr (k + 1) - qr k := by
    have hk1 : height - 1 - k + 1 = height - k := by omega
    have hknext : height - (k + 1) = height - 1 - k := by omega
    have hi := hPi (width + (height - 1 - k)) (width + k + 1)
      (by omega) (by omega)
    have hj := hPj (width + (height - k)) (width + k)
    have ha : width + (height - 1 - k) + 1 =
        width + (height - k) := by omega
    rw [ha] at hi
    dsimp only [qr]
    simp only [hknext, hk1, Nat.add_assoc]
    linear_combination hi - hj
  have htop (k : Nat) (hk : k < width) :
      -H (i0 + (width - 1 - k))
          (j0 + height + (width - 1 - k) + 1) -
          V (i0 + (width - 1 - k))
            (j0 + height + (width - 1 - k)) =
        qt (k + 1) - qt k := by
    have hk1 : width - 1 - k + 1 = width - k := by omega
    have hknext : width - (k + 1) = width - 1 - k := by omega
    have hi := hPi (width - 1 - k) (height + (width - k))
      (by omega) (by omega)
    have hj := hPj (width - 1 - k) (height + (width - 1 - k))
    have hb : height + (width - 1 - k) + 1 =
        height + (width - k) := by omega
    rw [hk1] at hi
    rw [hb] at hj
    dsimp only [qt]
    simp only [hknext, Nat.add_assoc]
    rw [hk1]
    linear_combination hi + hj
  have hleft (k : Nat) (hk : k < height) :
      -V (i0 + k) (j0 + (height - 1 - k)) +
          H (i0 + k) (j0 + (height - 1 - k)) =
        ql (k + 1) - ql k := by
    have hk1 : height - 1 - k + 1 = height - k := by omega
    have hknext : height - (k + 1) = height - 1 - k := by omega
    have hi := hPi k (height - 1 - k) (by omega) (by omega)
    have hj := hPj k (height - 1 - k)
    rw [hk1] at hj
    dsimp only [ql]
    simp only [hknext]
    linear_combination -hi + hj
  have hbottomSum :
      (∑ k ∈ Finset.range width,
        (H (i0 + height + k) (j0 + k) +
          V (i0 + height + k + 1) (j0 + k))) =
        qb width - qb 0 := by
    calc
      _ = ∑ k ∈ Finset.range width, (qb (k + 1) - qb k) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact hbottom k (Finset.mem_range.mp hk)
      _ = qb width - qb 0 := by
        simpa using sum_range_add_one_sub qb 0 width
  have hrightSum :
      (∑ k ∈ Finset.range height,
        (V (i0 + width + (height - 1 - k) + 1) (j0 + width + k) -
          H (i0 + width + (height - 1 - k)) (j0 + width + k + 1))) =
        qr height - qr 0 := by
    calc
      _ = ∑ k ∈ Finset.range height, (qr (k + 1) - qr k) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact hright k (Finset.mem_range.mp hk)
      _ = qr height - qr 0 := by
        simpa using sum_range_add_one_sub qr 0 height
  have htopSum :
      (∑ k ∈ Finset.range width,
        (-H (i0 + (width - 1 - k))
            (j0 + height + (width - 1 - k) + 1) -
          V (i0 + (width - 1 - k))
            (j0 + height + (width - 1 - k)))) =
        qt width - qt 0 := by
    calc
      _ = ∑ k ∈ Finset.range width, (qt (k + 1) - qt k) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact htop k (Finset.mem_range.mp hk)
      _ = qt width - qt 0 := by
        simpa using sum_range_add_one_sub qt 0 width
  have hleftSum :
      (∑ k ∈ Finset.range height,
        (-V (i0 + k) (j0 + (height - 1 - k)) +
          H (i0 + k) (j0 + (height - 1 - k)))) =
        ql height - ql 0 := by
    calc
      _ = ∑ k ∈ Finset.range height, (ql (k + 1) - ql k) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact hleft k (Finset.mem_range.mp hk)
      _ = ql height - ql 0 := by
        simpa using sum_range_add_one_sub ql 0 height
  unfold reflectedRadialAxisStaircaseBoundaryIntegral
  change (∑ k ∈ Finset.range width,
      (H (i0 + height + k) (j0 + k) +
        V (i0 + height + k + 1) (j0 + k))) +
    (∑ k ∈ Finset.range height,
      (V (i0 + width + (height - 1 - k) + 1) (j0 + width + k) -
        H (i0 + width + (height - 1 - k)) (j0 + width + k + 1))) +
    (∑ k ∈ Finset.range width,
      (-H (i0 + (width - 1 - k))
          (j0 + height + (width - 1 - k) + 1) -
        V (i0 + (width - 1 - k))
          (j0 + height + (width - 1 - k)))) +
    (∑ k ∈ Finset.range height,
      (-V (i0 + k) (j0 + (height - 1 - k)) +
        H (i0 + k) (j0 + (height - 1 - k)))) = 0
  rw [hbottomSum, hrightSum, htopSum, hleftSum]
  dsimp only [qb, qr, qt, ql]
  simp
  ring


end
end StatMech.Universality
