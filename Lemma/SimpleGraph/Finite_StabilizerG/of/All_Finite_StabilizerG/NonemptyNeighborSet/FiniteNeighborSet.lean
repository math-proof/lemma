import Mathlib
import sympy.Basic
import Def.CerednikDrinfeld_MumfordPeriod
import Lemma.Int.P2MUtil

open CerednikDrinfeld CerednikDrinfeld.Mumford MulAction

/--
[CerednikDrinfeld_Mumford_finite_stabilizer_of_finite_stabilizer_dart](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_CerednikDrinfeld_Mumford_finite_stabilizer_of_finite_stabilizer_dart.lean)
-/
@[path]
private lemma main
  [Group G] [MulAction G W]
  {𝒯 : SimpleGraph W} [GraphAction G 𝒯]
  {v : W}
-- given
  (hfin : (𝒯.neighborSet v).Finite)
  (hne : (𝒯.neighborSet v).Nonempty)
  (hD : ∀ d : 𝒯.Dart, d.fst = v → Finite (stabilizer G d)) :
-- imply
  Finite (stabilizer G v) := by
-- proof
  classical
  obtain ⟨w₀, hw₀⟩ := hne
  have hadj : 𝒯.Adj v w₀ := hw₀
  let d₀ : 𝒯.Dart := ⟨(v, w₀), hadj⟩
  have hfd : Finite (stabilizer G d₀) := hD d₀ rfl
  let H : Subgroup G := stabilizer G v
  let K : Subgroup ↥H := stabilizer (↥H) w₀
  have hKfin : Finite ↥K := by
    refine Finite.of_injective (fun k : ↥K => (⟨((k : ↥H) : G), ?_⟩ : stabilizer G d₀)) ?_
    ·
      show ((k : ↥H) : G) • d₀ = d₀
      have h1 : ((k : ↥H) : G) • v = v := (k : ↥H).2
      have h2 : ((k : ↥H) : G) • w₀ = w₀ := k.2
      refine SimpleGraph.Dart.ext _ _ (Prod.ext h1 h2)
    ·
      intro k₁ k₂ h
      apply Subtype.ext; apply Subtype.ext
      exact congrArg (fun z : ↥(stabilizer G d₀) => (z : G)) h
  have horb : orbit (↥H) w₀ ⊆ 𝒯.neighborSet v := by
    rintro w ⟨h, rfl⟩
    show 𝒯.Adj v (((h : ↥H) : G) • w₀)
    have hv : ((h : ↥H) : G) • v = v := h.2
    conv_lhs => rw [← hv]
    exact GraphAction.smul_adj _ hadj
  have : Finite ↑(orbit (↥H) w₀) := Set.Finite.subset hfin horb
  have hQ : Finite (↥H ⧸ K) := Finite.of_equiv _ (orbitEquivQuotientStabilizer (↥H) w₀)
  have : Finite ↥K := hKfin
  have : Finite ↥H := Finite.of_equiv _ (Subgroup.groupEquivQuotientProdSubgroup (s := K)).symm
  exact this


-- created on 2026-10-23
-- updated on 2026-10-24
