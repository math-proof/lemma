import Lemma.Random.Ne_0.of.Ne_0.Measurable
import Lemma.Random.SinglePSpace.of.AEMeasurable.Le
open MeasureTheory Random Fun


/--
A nonzero atom of a length-`n` random vector stays nonzero on a prefix:
`ℙ(x[:n] = «x.bvar»[:n]) ≠ 0` and `t ≤ n` give
`ℙ(x[:t] = «x.bvar»[:t]) ≠ 0`.

Python: Random.Ne_0.Slice.of.Ne_0, for `index = slice(0, t)` on a random
vector of shape `(n,)`.
-/
@[path]
private lemma main
  [MeasurableSpace Ω]
  [CountableMeasure α]
  [Countable α]
  [MeasurableSingletonClass α]
  {π : Measure Ω}
  {x : ℕ ⇀ Ω → α} {«x.bvar» : ℕ ⇀ α} {n : ℕ} [SinglePSpace π x[:n]]
-- given
  (t : ℕ)
  (ht : t ≤ n)
  (h : ℙ[π](x[:n] = «x.bvar»[:n]) ≠ 0) :
-- imply
  have : SinglePSpace π x[:t] :=
    SinglePSpace.of.AEMeasurable.Le t ht ‹SinglePSpace π x[:n]›.aemeasurable
  ℙ[π](x[:t] = «x.bvar»[:t]) ≠ 0 := by
-- proof
  intro hxt
  let g : (Fin n → α) → Fin t → α := fun v => v ∘ Fin.castLE ht
  have hg : Measurable g :=
    Measurable.of_eval fun i => measurable_pi_apply (Fin.castLE ht i)
  let x₀ : Ω → Fin n → α := (‹SinglePSpace π x[:n]›.aemeasurable).mk x[:n]
  have hx₀ : Measurable x₀ := ‹SinglePSpace π x[:n]›.aemeasurable.measurable_mk
  have : SinglePSpace π x₀ :=
    SinglePSpace.of.EqMeasureCount.Measurable hx₀ CountableMeasure.measure_eq_count
  have hgx : g ∘ x[:n] = x[:t] := by
    funext ω i
    rfl
  have hgv : g «x.bvar»[:n] = «x.bvar»[:t] := by
    funext i
    rfl
  have hmap : π.map x₀ = π.map x[:n] := by
    rw [← Measure.mapₗ_apply_of_measurable hx₀,
      Measure.mapₗ_mk_apply_of_aemeasurable ‹SinglePSpace π x[:n]›.aemeasurable]
  have h0 : π.prob x₀ «x.bvar»[:n] ≠ 0 := by
    unfold Measure.prob at h ⊢
    rwa [← hmap] at h
  have hne :=
    Ne_0.of.Ne_0.Measurable (x := x₀) (g := g) («x.bvar» := «x.bvar»[:n]) hx₀ hg h0
  have hmapt : π.map (g ∘ x₀) = π.map x[:t] := by
    rw [← hgx]
    apply Measure.map_congr
    apply (‹SinglePSpace π x[:n]›.aemeasurable.ae_eq_mk.fun_comp g).symm
  unfold Measure.prob
  rwa [← hgv, ← hmapt]


-- created on 2021-07-23
-- updated on 2026-10-23
