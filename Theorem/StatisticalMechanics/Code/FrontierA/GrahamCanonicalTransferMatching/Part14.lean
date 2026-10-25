/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferComponentCut.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc7componenteven
import Def.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferMatching.Part14
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem canonicalCoverageExclusiveBadQuadrangle_boundaryCertificate
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ e ∈ m, ¬ (ends e).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (a b c : leftMaskFiber ends m j k l zero p)
    (hab : CanonicalMaskTransferOrbit ends m j k l zero p a b)
    (hc : c ∈ canonicalCoverageExclusiveBadQuadrangles
      ends m j k l zero p a b) :
    CanonicalCoverageExclusiveBoundaryCertificate
      ends m j k l zero p a b c := by
  simpa only [CanonicalCoverageExclusiveBoundaryCertificate] using
    (canonicalCoverageExclusiveBadQuadrangle_typedData
      hloop hjk hkl a b c hab hc).2.2.2.2.2


theorem canonicalMaskTransferAdjacent_oppositeRootCuts_or_twoCommonImages
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ e ∈ m, ¬ (ends e).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (x y : leftMaskFiber ends m j k l zero p)
    (hxyne : x ≠ y)
    (hxy : CanonicalMaskTransferAdjacent ends m j k l zero p x y) :
    (∃ a b : leftMaskFiber ends m j k l zero p,
        CanonicalTransferWorks ends m k zero a.1.1 x.1.1 ∧
        CanonicalTransferWorks ends m k zero b.1.1 y.1.1 ∧
        canonicalTranslatedRow ends m k zero a.1.1 x.1.1 =
          canonicalTranslatedRow ends m k zero b.1.1 y.1.1 ∧
        ¬ CanonicalTransferWorks ends m k zero b.1.1 x.1.1 ∧
        ¬ CanonicalTransferWorks ends m k zero a.1.1 y.1.1 ∧
        CanonicalTranslatedRowRootComponentCut
          ends m k zero b.1.1 x.1.1 ∧
        CanonicalTranslatedRowRootComponentCut
          ends m k zero a.1.1 y.1.1) ∨
      ∃ q₁ q₂ : rightMaskFiber ends m j k l zero p,
        q₁ ≠ q₂ ∧
        q₁ ∈ canonicalMaskRightImages ends m j k l zero p x ∧
        q₁ ∈ canonicalMaskRightImages ends m j k l zero p y ∧
        q₂ ∈ canonicalMaskRightImages ends m j k l zero p x ∧
        q₂ ∈ canonicalMaskRightImages ends m j k l zero p y := by
  obtain ⟨a, b, hax, hby, hrow⟩ :=
    (canonicalMaskTransferAdjacent_iff_exists_works_rowSymmDiff
      hloop hjk hkl x y).mp hxy
  have htrans : canonicalTranslatedRow ends m k zero a.1.1 x.1.1 =
      canonicalTranslatedRow ends m k zero b.1.1 y.1.1 := hrow
  have hopp := canonicalTransferWorks_opposite_iff_of_translatedRow_eq
    hloop hjk hkl a b x y htrans
  by_cases hbx : CanonicalTransferWorks ends m k zero b.1.1 x.1.1
  · exact Or.inr (exists_two_common_canonicalMaskRightImages_of_collisionSquare
      hloop hjk hkl a b x y hxyne hax htrans hbx)
  · have hay : ¬ CanonicalTransferWorks ends m k zero a.1.1 y.1.1 :=
      fun hay => hbx (hopp.mpr hay)
    exact Or.inl ⟨a, b, hax, hby, htrans, hbx, hay,
      canonicalTransferWorks_failed_rootComponentCut
        hloop hjk hkl b x hbx,
      canonicalTransferWorks_failed_rootComponentCut
        hloop hjk hkl a y hay⟩


theorem exists_collisionReferenceDifference_at_adjacentFailedCutCrossing
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ e ∈ m, ¬ (ends e).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (r x y : leftMaskFiber ends m j k l zero p)
    (hxy : CanonicalMaskTransferAdjacent ends m j k l zero p x y)
    (hrx : CanonicalTransferWorks ends m k zero r.1.1 x.1.1)
    (hry : ¬ CanonicalTransferWorks ends m k zero r.1.1 y.1.1) :
    ∃ a b : leftMaskFiber ends m j k l zero p,
      CanonicalTransferWorks ends m k zero a.1.1 x.1.1 ∧
      CanonicalTransferWorks ends m k zero b.1.1 y.1.1 ∧
      canonicalTranslatedRow ends m k zero a.1.1 x.1.1 =
        canonicalTranslatedRow ends m k zero b.1.1 y.1.1 ∧
      ∃ e : I,
        e ∈ canonicalTransferUnion ends m k zero a.1.1 ∆
          canonicalTransferUnion ends m k zero b.1.1 ∧
        let Kx := canonicalTranslatedRow ends m k zero r.1.1 x.1.1
        let Ky := canonicalTranslatedRow ends m k zero r.1.1 y.1.1
        ((e ∈ Ky \ Kx ∧
            ∃ u v, u ∈ ends e ∧ v ∈ ends e ∧
              u ∉ StatMech.FrontierA.grahamComponentComplement
                ends Kx k ∧
              v ∈ StatMech.FrontierA.grahamComponentComplement
                ends Kx k) ∨
          (e ∈ (m \ Ky) \ (m \ Kx) ∧
            ∃ u v, u ∈ ends e ∧ v ∈ ends e ∧
              u ∉ StatMech.FrontierA.grahamComponentComplement
                ends (m \ Kx) k ∧
              v ∈ StatMech.FrontierA.grahamComponentComplement
                ends (m \ Kx) k)) := by
  obtain ⟨a, b, hax, hby, htrans⟩ :=
    (canonicalMaskTransferAdjacent_iff_exists_works_rowSymmDiff
      hloop hjk hkl x y).mp hxy
  let Kx := canonicalTranslatedRow ends m k zero r.1.1 x.1.1
  let Ky := canonicalTranslatedRow ends m k zero r.1.1 y.1.1
  have hKx : RowSupportDisconnects ends m Kx k zero :=
    (canonicalTransferWorks_iff_translatedRowDisconnects
      hloop hjk hkl r x).mp hrx
  have hKy : ¬ RowSupportDisconnects ends m Ky k zero :=
    fun h => hry ((canonicalTransferWorks_iff_translatedRowDisconnects
      hloop hjk hkl r y).mpr h)
  have hdiff : Kx ∆ Ky =
      canonicalTransferUnion ends m k zero a.1.1 ∆
        canonicalTransferUnion ends m k zero b.1.1 := by
    calc
      Kx ∆ Ky = rowClass m x.1.1 0 ∆ rowClass m y.1.1 0 := by
        dsimp only [Kx, Ky, canonicalTranslatedRow]
        calc
          (rowClass m x.1.1 0 ∆
              canonicalTransferUnion ends m k zero r.1.1) ∆
              (rowClass m y.1.1 0 ∆
                canonicalTransferUnion ends m k zero r.1.1) =
            (rowClass m x.1.1 0 ∆ rowClass m y.1.1 0) ∆
              (canonicalTransferUnion ends m k zero r.1.1 ∆
                canonicalTransferUnion ends m k zero r.1.1) := by ac_rfl
          _ = rowClass m x.1.1 0 ∆ rowClass m y.1.1 0 := by simp
      _ = canonicalTransferUnion ends m k zero a.1.1 ∆
          canonicalTransferUnion ends m k zero b.1.1 :=
        rowSymmDiff_eq_transferSymmDiff_of_translatedRow_eq
          a.1.1 b.1.1 x.1.1 y.1.1 htrans
  refine ⟨a, b, hax, hby, htrans, ?_⟩
  by_cases hconn : StatMech.Sharpness.RandomCurrent.connK
      ends Ky k zero
  · let S := StatMech.FrontierA.grahamComponentComplement ends Kx k
    have hkS : k ∉ S :=
      StatMech.FrontierA.grahamComponentComplement_not_mem ends Kx k
    have hzeroS : zero ∈ S := by
      dsimp only [S]
      rw [StatMech.FrontierA.grahamComponentComplement,
        StatMech.Sharpness.RandomCurrent.mem_notConnCompK]
      exact hKx.1
    obtain ⟨e, he, hcross⟩ := exists_crossing_edge_mem_sdiff_of_connK
      (StatMech.FrontierA.grahamComponentComplement_noCrossing
        ends Kx k) hkS hzeroS hconn
    have he' := Finset.mem_sdiff.mp he
    have heDiff : e ∈ Kx ∆ Ky :=
      Finset.mem_symmDiff.mpr (Or.inr ⟨he'.1, he'.2⟩)
    refine ⟨e, hdiff ▸ heDiff, ?_⟩
    dsimp only [Kx, Ky]
    exact Or.inl ⟨he, hcross⟩
  · have hconnComp : StatMech.Sharpness.RandomCurrent.connK
        ends (m \ Ky) k zero := by
      by_contra hnot
      exact hKy ⟨hconn, hnot⟩
    let S := StatMech.FrontierA.grahamComponentComplement
      ends (m \ Kx) k
    have hkS : k ∉ S :=
      StatMech.FrontierA.grahamComponentComplement_not_mem
        ends (m \ Kx) k
    have hzeroS : zero ∈ S := by
      dsimp only [S]
      rw [StatMech.FrontierA.grahamComponentComplement,
        StatMech.Sharpness.RandomCurrent.mem_notConnCompK]
      exact hKx.2
    obtain ⟨e, he, hcross⟩ := exists_crossing_edge_mem_sdiff_of_connK
      (StatMech.FrontierA.grahamComponentComplement_noCrossing
        ends (m \ Kx) k) hkS hzeroS hconnComp
    have he' := Finset.mem_sdiff.mp he
    have heKy := Finset.mem_sdiff.mp he'.1
    have heNotKx : e ∉ Ky := by
      intro heKyMem
      exact heKy.2 heKyMem
    have heKx : e ∈ Kx := by
      by_contra heKx
      exact he'.2 (Finset.mem_sdiff.mpr ⟨heKy.1, heKx⟩)
    have heDiff : e ∈ Kx ∆ Ky :=
      Finset.mem_symmDiff.mpr (Or.inl ⟨heKx, heNotKx⟩)
    refine ⟨e, hdiff ▸ heDiff, ?_⟩
    dsimp only [Kx, Ky]
    exact Or.inr ⟨he, hcross⟩


theorem exists_rootIncident_transferDifference_of_equalNormal_failed
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ e ∈ m, ¬ (ends e).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    {p : Finset I × Finset I}
    (r c : leftMaskFiber ends m j k l zero p)
    (hnormal : canonicalNormalRow ends m k zero r.1.1 =
      canonicalNormalRow ends m k zero c.1.1)
    (hbad : ¬ CanonicalTransferWorks ends m k zero r.1.1 c.1.1) :
    ∃ e : I,
      e ∈ canonicalTransferUnion ends m k zero r.1.1 ∆
        canonicalTransferUnion ends m k zero c.1.1 ∧
      let N := canonicalNormalRow ends m k zero r.1.1
      let K := canonicalTranslatedRow ends m k zero r.1.1 c.1.1
      ((e ∈ K \ N ∧ zero ∈ ends e) ∨
        (e ∈ (m \ K) \ (m \ N) ∧ k ∈ ends e)) := by
  let N := canonicalNormalRow ends m k zero r.1.1
  let K := canonicalTranslatedRow ends m k zero r.1.1 c.1.1
  have hN : N = rowClass m c.1.1 0 ∆
      canonicalTransferUnion ends m k zero c.1.1 := by
    simpa only [N, canonicalNormalRow] using hnormal
  have hdiff : K ∆ N =
      canonicalTransferUnion ends m k zero r.1.1 ∆
        canonicalTransferUnion ends m k zero c.1.1 := by
    dsimp only [K, canonicalTranslatedRow]
    rw [hN]
    calc
      (rowClass m c.1.1 0 ∆
          canonicalTransferUnion ends m k zero r.1.1) ∆
          (rowClass m c.1.1 0 ∆
            canonicalTransferUnion ends m k zero c.1.1) =
        (rowClass m c.1.1 0 ∆ rowClass m c.1.1 0) ∆
          (canonicalTransferUnion ends m k zero r.1.1 ∆
            canonicalTransferUnion ends m k zero c.1.1) := by ac_rfl
      _ = canonicalTransferUnion ends m k zero r.1.1 ∆
          canonicalTransferUnion ends m k zero c.1.1 := by simp
  have hK : ¬ RowSupportDisconnects ends m K k zero :=
    fun h => hbad ((canonicalTransferWorks_iff_translatedRowDisconnects
      hloop hjk hkl r c).mpr h)
  have hNzero : ∀ e ∈ N, zero ∉ ends e := by
    simpa only [N] using
      canonicalNormalRow_no_incident_zero hloop hjk hkl r.1.2
  have hNcompK : ∀ e ∈ m \ N, k ∉ ends e := by
    intro e he hek
    have he' := Finset.mem_sdiff.mp he
    exact he'.2 (by
      simpa only [N] using
        (mem_canonicalNormalRow_of_mem_k
          hloop hjk hkl r.1.2 he'.1 hek))
  by_cases hconn : StatMech.Sharpness.RandomCurrent.connK
      ends K k zero
  · have hno : StatMech.Sharpness.RandomCurrent.NoCrossingK
        ends N {zero} := by
      intro e he
      right
      intro w hw
      simp only [Finset.mem_compl, Finset.mem_singleton]
      exact fun hw0 => hNzero e he (hw0 ▸ hw)
    obtain ⟨e, he, u, v, hu, hv, -, hvS⟩ :=
      exists_crossing_edge_mem_sdiff_of_connK
        hno (by simpa [hk0]) (by simp) hconn
    have hvzero : v = zero := by simpa using hvS
    have hzeroEnd : zero ∈ ends e := by simpa [hvzero] using hv
    have he' := Finset.mem_sdiff.mp he
    have heDiff : e ∈ K ∆ N :=
      Finset.mem_symmDiff.mpr (Or.inl ⟨he'.1, he'.2⟩)
    refine ⟨e, hdiff ▸ heDiff, ?_⟩
    dsimp only [N, K]
    exact Or.inl ⟨he, hzeroEnd⟩
  · have hconnComp : StatMech.Sharpness.RandomCurrent.connK
        ends (m \ K) k zero := by
      by_contra hnot
      exact hK ⟨hconn, hnot⟩
    have hno : StatMech.Sharpness.RandomCurrent.NoCrossingK
        ends (m \ N) {k} := by
      intro e he
      right
      intro w hw
      simp only [Finset.mem_compl, Finset.mem_singleton]
      exact fun hwk => hNcompK e he (hwk ▸ hw)
    obtain ⟨e, he, u, v, hu, hv, -, hvS⟩ :=
      exists_crossing_edge_mem_sdiff_of_connK
        hno (by simpa using Ne.symm hk0) (by simp)
          (StatMech.Sharpness.RandomCurrent.connK_symm
            ends (m \ K) hconnComp)
    have hvk : v = k := by simpa using hvS
    have hkEnd : k ∈ ends e := by simpa [hvk] using hv
    have he' := Finset.mem_sdiff.mp he
    have heKcomp := Finset.mem_sdiff.mp he'.1
    have heNcomp : e ∉ m \ N := he'.2
    have heN : e ∈ N := by
      by_contra heNotN
      exact heNcomp (Finset.mem_sdiff.mpr ⟨heKcomp.1, heNotN⟩)
    have heNotK : e ∉ K := heKcomp.2
    have heDiff : e ∈ K ∆ N :=
      Finset.mem_symmDiff.mpr (Or.inr ⟨heN, heNotK⟩)
    refine ⟨e, hdiff ▸ heDiff, ?_⟩
    dsimp only [N, K]
    exact Or.inr ⟨he, hkEnd⟩


theorem canonicalMaskTransferOrbitInternallyComplete_of_adjacentWorksPropagates
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hprop : CanonicalMaskAdjacentWorksPropagates
      ends m j k l zero p) :
    CanonicalMaskTransferOrbitInternallyComplete
      ends m j k l zero p := by
  intro r c hrc
  induction hrc with
  | refl => exact canonicalTransferWorks_self hloop hjk hkl hk0 r
  | @tail x y _ hxy ih => exact hprop r x y hxy ih


theorem canonicalMaskTransferOrbitInternallyComplete_of_normalGeometry
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (hinvariant : CanonicalMaskAdjacentNormalInvariant
      ends m j k l zero p)
    (hcomplete : CanonicalMaskNormalFiberComplete
      ends m j k l zero p) :
    CanonicalMaskTransferOrbitInternallyComplete
      ends m j k l zero p := by
  intro r c hrc
  apply hcomplete r c
  induction hrc with
  | refl => rfl
  | @tail x y _ hxy ih => exact ih.trans (hinvariant x y hxy)


theorem exists_adjacent_normalRow_ne_of_orbit_normalRow_ne
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (r c : leftMaskFiber ends m j k l zero p)
    (hrc : CanonicalMaskTransferOrbit ends m j k l zero p r c)
    (hne : canonicalNormalRow ends m k zero r.1.1 ≠
      canonicalNormalRow ends m k zero c.1.1) :
    ∃ x y : leftMaskFiber ends m j k l zero p,
      CanonicalMaskTransferOrbit ends m j k l zero p r x ∧
      CanonicalMaskTransferAdjacent ends m j k l zero p x y ∧
      canonicalNormalRow ends m k zero x.1.1 ≠
        canonicalNormalRow ends m k zero y.1.1 := by
  have extract : ∀ {d : leftMaskFiber ends m j k l zero p},
      CanonicalMaskTransferOrbit ends m j k l zero p r d ->
      canonicalNormalRow ends m k zero r.1.1 ≠
        canonicalNormalRow ends m k zero d.1.1 ->
      ∃ x y : leftMaskFiber ends m j k l zero p,
        CanonicalMaskTransferOrbit ends m j k l zero p r x ∧
        CanonicalMaskTransferAdjacent ends m j k l zero p x y ∧
        canonicalNormalRow ends m k zero x.1.1 ≠
          canonicalNormalRow ends m k zero y.1.1 := by
    intro d hrd
    induction hrd with
    | refl => exact fun hne => False.elim (hne rfl)
    | @tail x y hrx hxy ih =>
        intro hne
        by_cases hstep : canonicalNormalRow ends m k zero x.1.1 =
            canonicalNormalRow ends m k zero y.1.1
        · exact ih (fun hrxEq => hne (hrxEq.trans hstep))
        · exact ⟨x, y, hrx, hxy, hstep⟩
  exact extract hrc hne


theorem exists_adjacent_works_failed_of_orbit_failed
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (r c : leftMaskFiber ends m j k l zero p)
    (hself : CanonicalTransferWorks ends m k zero r.1.1 r.1.1)
    (hrc : CanonicalMaskTransferOrbit ends m j k l zero p r c)
    (hbad : ¬ CanonicalTransferWorks ends m k zero r.1.1 c.1.1) :
    ∃ x y : leftMaskFiber ends m j k l zero p,
      CanonicalMaskTransferOrbit ends m j k l zero p r x ∧
      CanonicalMaskTransferAdjacent ends m j k l zero p x y ∧
      CanonicalTransferWorks ends m k zero r.1.1 x.1.1 ∧
      ¬ CanonicalTransferWorks ends m k zero r.1.1 y.1.1 := by
  have extract : ∀ {d : leftMaskFiber ends m j k l zero p},
      CanonicalMaskTransferOrbit ends m j k l zero p r d ->
      ¬ CanonicalTransferWorks ends m k zero r.1.1 d.1.1 ->
      ∃ x y : leftMaskFiber ends m j k l zero p,
        CanonicalMaskTransferOrbit ends m j k l zero p r x ∧
        CanonicalMaskTransferAdjacent ends m j k l zero p x y ∧
        CanonicalTransferWorks ends m k zero r.1.1 x.1.1 ∧
        ¬ CanonicalTransferWorks ends m k zero r.1.1 y.1.1 := by
    intro d hrd
    induction hrd with
    | refl =>
        intro hbad
        exact False.elim (hbad hself)
    | @tail x y hrx hxy ih =>
        intro hbad
        by_cases hx : CanonicalTransferWorks
            ends m k zero r.1.1 x.1.1
        · exact ⟨x, y, hrx, hxy, hx, hbad⟩
        · exact ih hx
  exact extract hrc hbad


theorem canonicalMaskRightHall_of_orbitInternallyComplete
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (p : Finset I × Finset I)
    (hcomplete : CanonicalMaskTransferOrbitInternallyComplete
      ends m j k l zero p) :
    CanonicalMaskRightHall ends m j k l zero p := by
  classical
  let rho := canonicalMaskOrbitMinimumReference ends m j k l zero p
  have hrho : IsCanonicalMaskOrbitSelector ends m j k l zero p rho :=
    canonicalMaskOrbitMinimumReference_selector ends m j k l zero p
  have hworks : ∀ c : leftMaskFiber ends m j k l zero p,
      CanonicalTransferWorks ends m k zero (rho c).1.1 c.1.1 := by
    intro c
    exact hcomplete (rho c) c
      (canonicalMaskTransferOrbit_symm ends m j k l zero p (hrho.1 c))
  let f := canonicalOrbitSelectorMaskFiberEmbedding
    ends m j k l zero hloop hjk hkl p rho hrho hworks
  rw [canonicalMaskRightHall_iff_exists_matching]
  refine ⟨f, ?_⟩
  intro c
  rw [mem_canonicalMaskRightImages_iff]
  exact ⟨rho c, hworks c, rfl⟩


theorem canonicalMaskRightHall_of_adjacentWorksPropagates
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hprop : CanonicalMaskAdjacentWorksPropagates
      ends m j k l zero p) :
    CanonicalMaskRightHall ends m j k l zero p :=
  canonicalMaskRightHall_of_orbitInternallyComplete
    ends m j k l zero hloop hjk hkl p
      (canonicalMaskTransferOrbitInternallyComplete_of_adjacentWorksPropagates
        ends m j k l zero hloop hjk hkl hk0 p hprop)


theorem canonicalMaskRightHall_of_normalGeometry
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (p : Finset I × Finset I)
    (hinvariant : CanonicalMaskAdjacentNormalInvariant
      ends m j k l zero p)
    (hcomplete : CanonicalMaskNormalFiberComplete
      ends m j k l zero p) :
    CanonicalMaskRightHall ends m j k l zero p :=
  canonicalMaskRightHall_of_orbitInternallyComplete
    ends m j k l zero hloop hjk hkl p
      (canonicalMaskTransferOrbitInternallyComplete_of_normalGeometry
        ends m j k l zero p hinvariant hcomplete)


theorem GrahamFiberMinor_of_orbitInternallyComplete
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (hcomplete : ∀ p : Finset I × Finset I,
      CanonicalMaskTransferOrbitInternallyComplete
        ends m j k l zero p) :
    GrahamFiberMinor ends m j k l zero := by
  apply GrahamFiberMinor_of_canonicalMaskRightHall
  intro p
  exact canonicalMaskRightHall_of_orbitInternallyComplete
    ends m j k l zero hloop hjk hkl p (hcomplete p)


theorem GrahamFiberMinor_of_adjacentWorksPropagates
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (hprop : ∀ p : Finset I × Finset I,
      CanonicalMaskAdjacentWorksPropagates
        ends m j k l zero p) :
    GrahamFiberMinor ends m j k l zero := by
  apply GrahamFiberMinor_of_canonicalMaskRightHall
  intro p
  exact canonicalMaskRightHall_of_adjacentWorksPropagates
    ends m j k l zero hloop hjk hkl hk0 p (hprop p)


theorem GrahamFiberMinor_of_normalGeometry
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (hinvariant : ∀ p : Finset I × Finset I,
      CanonicalMaskAdjacentNormalInvariant
        ends m j k l zero p)
    (hcomplete : ∀ p : Finset I × Finset I,
      CanonicalMaskNormalFiberComplete
        ends m j k l zero p) :
    GrahamFiberMinor ends m j k l zero := by
  apply GrahamFiberMinor_of_canonicalMaskRightHall
  intro p
  exact canonicalMaskRightHall_of_normalGeometry
    ends m j k l zero hloop hjk hkl p
      (hinvariant p) (hcomplete p)


theorem exists_orbitInternal_rootComponentCut_of_not_canonicalMaskRightHall
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (hfail : ¬ CanonicalMaskRightHall ends m j k l zero p) :
    ∃ r c : leftMaskFiber ends m j k l zero p,
      CanonicalMaskTransferOrbit ends m j k l zero p r c ∧
      ¬ CanonicalTransferWorks ends m k zero r.1.1 c.1.1 ∧
      CanonicalTranslatedRowRootComponentCut
        ends m k zero r.1.1 c.1.1 := by
  obtain ⟨S, a, r, c, -, -, -, -, -, haSorbit, har, -, hcS, -,
      hcNotCoverage, hcut⟩ :=
    exists_maximalOrbitCoverage_rootComponentCut_of_not_canonicalMaskRightHall
      ends m j k l zero hloop hjk hkl hk0 p hfail
  have hrc : CanonicalMaskTransferOrbit ends m j k l zero p r c :=
    (canonicalMaskTransferOrbit_symm ends m j k l zero p har).trans
      (haSorbit c hcS)
  refine ⟨r, c, hrc, ?_, hcut⟩
  intro hworks
  exact hcNotCoverage ((mem_canonicalMaskOrbitCoverage_iff
    ends m j k l zero p r c).mpr ⟨hrc, hworks⟩)


theorem exists_normalGeometry_obstruction_of_not_canonicalMaskRightHall
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (hfail : ¬ CanonicalMaskRightHall ends m j k l zero p) :
    (∃ x y : leftMaskFiber ends m j k l zero p,
        CanonicalMaskTransferAdjacent ends m j k l zero p x y ∧
        canonicalNormalRow ends m k zero x.1.1 ≠
          canonicalNormalRow ends m k zero y.1.1) ∨
      ∃ r c : leftMaskFiber ends m j k l zero p,
        canonicalNormalRow ends m k zero r.1.1 =
          canonicalNormalRow ends m k zero c.1.1 ∧
        ¬ CanonicalTransferWorks ends m k zero r.1.1 c.1.1 ∧
        CanonicalTranslatedRowRootComponentCut
          ends m k zero r.1.1 c.1.1 := by
  obtain ⟨r, c, hrc, hbad, hcut⟩ :=
    exists_orbitInternal_rootComponentCut_of_not_canonicalMaskRightHall
      ends m j k l zero hloop hjk hkl hk0 p hfail
  by_cases hnormal : canonicalNormalRow ends m k zero r.1.1 =
      canonicalNormalRow ends m k zero c.1.1
  · exact Or.inr ⟨r, c, hnormal, hbad, hcut⟩
  · obtain ⟨x, y, -, hxy, hne⟩ :=
      exists_adjacent_normalRow_ne_of_orbit_normalRow_ne
        ends m j k l zero p r c hrc hnormal
    exact Or.inl ⟨x, y, hxy, hne⟩


theorem exists_adjacent_orbitInternal_rootComponentCut_of_not_canonicalMaskRightHall
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (hfail : ¬ CanonicalMaskRightHall ends m j k l zero p) :
    ∃ r x y : leftMaskFiber ends m j k l zero p,
      CanonicalMaskTransferOrbit ends m j k l zero p r x ∧
      CanonicalMaskTransferAdjacent ends m j k l zero p x y ∧
      CanonicalTransferWorks ends m k zero r.1.1 x.1.1 ∧
      ¬ CanonicalTransferWorks ends m k zero r.1.1 y.1.1 ∧
      CanonicalTranslatedRowRootComponentCut
        ends m k zero r.1.1 y.1.1 := by
  obtain ⟨r, c, hrc, hbad, -⟩ :=
    exists_orbitInternal_rootComponentCut_of_not_canonicalMaskRightHall
      ends m j k l zero hloop hjk hkl hk0 p hfail
  obtain ⟨x, y, hrx, hxy, hx, hy⟩ :=
    exists_adjacent_works_failed_of_orbit_failed
      ends m j k l zero p r c
        (canonicalTransferWorks_self hloop hjk hkl hk0 r) hrc hbad
  exact ⟨r, x, y, hrx, hxy, hx, hy,
    canonicalTransferWorks_failed_rootComponentCut
      hloop hjk hkl r y hy⟩


theorem exists_maximalCoverage_adjacentBoundary_quadrangleDichotomy_of_not_canonicalMaskRightHall
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (hfail : ¬ CanonicalMaskRightHall ends m j k l zero p) :
    ∃ r x y : leftMaskFiber ends m j k l zero p,
      CanonicalMaskOrbitCoverageMaximal ends m j k l zero p r ∧
      CanonicalMaskAdjacentCoverageBoundary ends m j k l zero p r x y ∧
      CanonicalTranslatedRowRootComponentCut
        ends m k zero r.1.1 y.1.1 ∧
      ((∃ d : leftMaskFiber ends m j k l zero p,
          d ∈ canonicalMaskOrbitCoverage ends m j k l zero p r ∧
          d ∉ canonicalMaskOrbitCoverage ends m j k l zero p y) ∨
        (y ∈ canonicalCoverageExclusiveBadQuadrangles
            ends m j k l zero p y r ∧
          ∃ d : leftMaskFiber ends m j k l zero p,
            d ∈ canonicalCoverageExclusiveBadQuadrangles
              ends m j k l zero p r y)) := by
  classical
  obtain ⟨S, a, r, c, -, -, -, -, -, haSorbit, har, hrMax, hcS, -,
      hcNotCoverage, -⟩ :=
    exists_maximalOrbitCoverage_rootComponentCut_of_not_canonicalMaskRightHall
      ends m j k l zero hloop hjk hkl hk0 p hfail
  have hrc : CanonicalMaskTransferOrbit ends m j k l zero p r c :=
    (canonicalMaskTransferOrbit_symm ends m j k l zero p har).trans
      (haSorbit c hcS)
  have hbad : ¬ CanonicalTransferWorks
      ends m k zero r.1.1 c.1.1 := by
    intro hworks
    exact hcNotCoverage ((mem_canonicalMaskOrbitCoverage_iff
      ends m j k l zero p r c).mpr ⟨hrc, hworks⟩)
  obtain ⟨x, y, hrx, hxy, hx, hy⟩ :=
    exists_adjacent_works_failed_of_orbit_failed
      ends m j k l zero p r c
        (canonicalTransferWorks_self hloop hjk hkl hk0 r) hrc hbad
  have hry : CanonicalMaskTransferOrbit ends m j k l zero p r y :=
    hrx.tail hxy
  have hyr : CanonicalMaskTransferOrbit ends m j k l zero p y r :=
    canonicalMaskTransferOrbit_symm ends m j k l zero p hry
  have hrMax' : CanonicalMaskOrbitCoverageMaximal
      ends m j k l zero p r := by
    intro t hrt
    exact hrMax t (har.trans hrt)
  have hyCoverage : y ∈ canonicalMaskOrbitCoverage
      ends m j k l zero p y :=
    (mem_canonicalMaskOrbitCoverage_iff
      ends m j k l zero p y y).mpr ⟨
        canonicalMaskTransferOrbit_refl ends m j k l zero p y,
        canonicalTransferWorks_self hloop hjk hkl hk0 y⟩
  have hyNotCoverage : y ∉ canonicalMaskOrbitCoverage
      ends m j k l zero p r := by
    rw [mem_canonicalMaskOrbitCoverage_iff]
    exact fun h => hy h.2
  refine ⟨r, x, y, hrMax', ⟨hrx, hxy, hx, hy⟩,
    canonicalTransferWorks_failed_rootComponentCut
      hloop hjk hkl r y hy, ?_⟩
  by_cases hdisc : RowsDisconnect ends m
      (canonicalQuadrangleCompletion ends m k zero
        y.1.1 r.1.1 y.1.1) k zero
  · let d := canonicalQuadrangleCompletionMemOfDisconnects
      ends m j k l zero hloop hjk hkl p y r y hdisc
    have hd := quadrangleCompletion_mem_coverage_sdiff
      hloop hjk hkl y r y hyr hyCoverage hyNotCoverage hdisc
    exact Or.inl ⟨d, hd.1, hd.2⟩
  · have hyBad : y ∈ canonicalCoverageExclusiveBadQuadrangles
        ends m j k l zero p y r := by
      rw [mem_canonicalCoverageExclusiveBadQuadrangles_iff]
      exact ⟨hyCoverage, hyNotCoverage, hdisc⟩
    have hcard := hrMax' y hry
    obtain ⟨d, hdBad⟩ :=
      exists_opposite_badQuadrangle_of_coverage_card_le
        hloop hjk hkl y r y hyr hyBad hcard
    exact Or.inr ⟨hyBad, d, hdBad⟩


theorem exists_maximalCoverage_adjacentBoundary_opposingCertificates_of_not_canonicalMaskRightHall
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (hfail : ¬ CanonicalMaskRightHall ends m j k l zero p) :
    ∃ r x y : leftMaskFiber ends m j k l zero p,
      CanonicalMaskOrbitCoverageMaximal ends m j k l zero p r ∧
      CanonicalMaskAdjacentCoverageBoundary ends m j k l zero p r x y ∧
      CanonicalTranslatedRowRootComponentCut
        ends m k zero r.1.1 y.1.1 ∧
      ((∃ d : leftMaskFiber ends m j k l zero p,
          d ∈ canonicalMaskOrbitCoverage ends m j k l zero p r ∧
          d ∉ canonicalMaskOrbitCoverage ends m j k l zero p y) ∨
        ∃ d : leftMaskFiber ends m j k l zero p,
          y ∈ canonicalCoverageExclusiveBadQuadrangles
            ends m j k l zero p y r ∧
          d ∈ canonicalCoverageExclusiveBadQuadrangles
            ends m j k l zero p r y ∧
          CanonicalCoverageExclusiveBoundaryCertificate
            ends m j k l zero p y r y ∧
          CanonicalCoverageExclusiveBoundaryCertificate
            ends m j k l zero p r y d) := by
  obtain ⟨r, x, y, hrMax, hboundary, hcut, hcase⟩ :=
    exists_maximalCoverage_adjacentBoundary_quadrangleDichotomy_of_not_canonicalMaskRightHall
      ends m j k l zero hloop hjk hkl hk0 p hfail
  refine ⟨r, x, y, hrMax, hboundary, hcut, ?_⟩
  rcases hcase with hdiff | ⟨hyBad, d, hdBad⟩
  · exact Or.inl hdiff
  · have hry : CanonicalMaskTransferOrbit ends m j k l zero p r y :=
      hboundary.1.tail hboundary.2.1
    have hyr : CanonicalMaskTransferOrbit ends m j k l zero p y r :=
      canonicalMaskTransferOrbit_symm ends m j k l zero p hry
    exact Or.inr ⟨d, hyBad, hdBad,
      canonicalCoverageExclusiveBadQuadrangle_boundaryCertificate
        hloop hjk hkl y r y hyr hyBad,
      canonicalCoverageExclusiveBadQuadrangle_boundaryCertificate
        hloop hjk hkl r y d hry hdBad⟩


theorem exists_maximalCoverage_adjacentBoundary_oppositeRootCuts_or_twoCommonImages_of_not_canonicalMaskRightHall
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (hfail : ¬ CanonicalMaskRightHall ends m j k l zero p) :
    ∃ r x y : leftMaskFiber ends m j k l zero p,
      CanonicalMaskOrbitCoverageMaximal ends m j k l zero p r ∧
      CanonicalMaskAdjacentCoverageBoundary ends m j k l zero p r x y ∧
      CanonicalTranslatedRowRootComponentCut
        ends m k zero r.1.1 y.1.1 ∧
      ((∃ a b : leftMaskFiber ends m j k l zero p,
          CanonicalTransferWorks ends m k zero a.1.1 x.1.1 ∧
          CanonicalTransferWorks ends m k zero b.1.1 y.1.1 ∧
          canonicalTranslatedRow ends m k zero a.1.1 x.1.1 =
            canonicalTranslatedRow ends m k zero b.1.1 y.1.1 ∧
          ¬ CanonicalTransferWorks ends m k zero b.1.1 x.1.1 ∧
          ¬ CanonicalTransferWorks ends m k zero a.1.1 y.1.1 ∧
          CanonicalTranslatedRowRootComponentCut
            ends m k zero b.1.1 x.1.1 ∧
          CanonicalTranslatedRowRootComponentCut
            ends m k zero a.1.1 y.1.1) ∨
        ∃ q₁ q₂ : rightMaskFiber ends m j k l zero p,
          q₁ ≠ q₂ ∧
          q₁ ∈ canonicalMaskRightImages ends m j k l zero p x ∧
          q₁ ∈ canonicalMaskRightImages ends m j k l zero p y ∧
          q₂ ∈ canonicalMaskRightImages ends m j k l zero p x ∧
          q₂ ∈ canonicalMaskRightImages ends m j k l zero p y) := by
  obtain ⟨r, x, y, hrMax, hboundary, hcut, -⟩ :=
    exists_maximalCoverage_adjacentBoundary_quadrangleDichotomy_of_not_canonicalMaskRightHall
      ends m j k l zero hloop hjk hkl hk0 p hfail
  have hxyne : x ≠ y := by
    intro hxy
    subst y
    exact hboundary.2.2.2 hboundary.2.2.1
  exact ⟨r, x, y, hrMax, hboundary, hcut,
    canonicalMaskTransferAdjacent_oppositeRootCuts_or_twoCommonImages
      hloop hjk hkl x y hxyne hboundary.2.1⟩


theorem exists_rootComponentCut_of_tight_canonicalMaskRightNeighborhood
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (p : Finset I × Finset I)
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (hSne : S.Nonempty)
    (htight : (canonicalMaskRightNeighborhood
      ends m j k l zero p S).card + 1 = S.card) :
    ∃ r ∈ S, ∃ c ∈ S,
      CanonicalTranslatedRowRootComponentCut
        ends m k zero r.1.1 c.1.1 := by
  classical
  obtain ⟨r, hrS⟩ := hSne
  by_cases hworks : ∀ c ∈ S,
      CanonicalTransferWorks ends m k zero r.1.1 c.1.1
  · have hle := card_le_canonicalMaskRightNeighborhood_of_reference
      ends m j k l zero hloop hjk hkl p S r hworks
    omega
  · push Not at hworks
    obtain ⟨c, hcS, hbad⟩ := hworks
    exact ⟨r, hrS, c, hcS,
      canonicalTransferWorks_failed_rootComponentCut
        hloop hjk hkl r c hbad⟩


theorem exists_distinctNormalRows_of_tight_canonicalMaskRightNeighborhood
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (p : Finset I × Finset I)
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (hSne : S.Nonempty)
    (htight : (canonicalMaskRightNeighborhood
      ends m j k l zero p S).card + 1 = S.card) :
    ∃ r ∈ S, ∃ c ∈ S,
      canonicalNormalRow ends m k zero r.1.1 ≠
        canonicalNormalRow ends m k zero c.1.1 := by
  obtain ⟨r, hrS, c, hcS, hcut⟩ :=
    exists_rootComponentCut_of_tight_canonicalMaskRightNeighborhood
      ends m j k l zero hloop hjk hkl p S hSne htight
  exact ⟨r, hrS, c, hcS,
    canonicalNormalRows_ne_of_rootComponentCut
      hloop hjk hkl r c hcut⟩


theorem exists_rootComponentCut_of_not_canonicalMaskRightHall
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (hfail : ¬ CanonicalMaskRightHall ends m j k l zero p) :
    ∃ S : Finset (leftMaskFiber ends m j k l zero p),
      ∃ r ∈ S, ∃ c ∈ S,
        CanonicalTranslatedRowRootComponentCut
          ends m k zero r.1.1 c.1.1 := by
  classical
  obtain ⟨S, hSne, htight, -, -, -, -⟩ :=
    exists_tight_canonicalMaskRightHall_obstruction
      ends m j k l zero hloop hjk hkl hk0 p hfail
  obtain ⟨r, hrS, c, hcS, hcut⟩ :=
    exists_rootComponentCut_of_tight_canonicalMaskRightNeighborhood
      ends m j k l zero hloop hjk hkl p S hSne htight
  exact ⟨S, r, hrS, c, hcS, hcut⟩


theorem canonicalMaskRightHall_of_no_rootComponentCut
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (hno : ∀ r c : leftMaskFiber ends m j k l zero p,
      ¬ CanonicalTranslatedRowRootComponentCut
        ends m k zero r.1.1 c.1.1) :
    CanonicalMaskRightHall ends m j k l zero p := by
  by_contra hfail
  obtain ⟨S, r, -, c, -, hcut⟩ :=
    exists_rootComponentCut_of_not_canonicalMaskRightHall
      ends m j k l zero hloop hjk hkl hk0 p hfail
  exact hno r c hcut


end StatMech.GrahamGHS.FourColor
