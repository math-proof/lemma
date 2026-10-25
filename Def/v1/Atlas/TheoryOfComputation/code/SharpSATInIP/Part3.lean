/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SharpSATInIP.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TheoryOfComputation.code.InteractiveProofs.Part2
import Def.v1.Atlas.TheoryOfComputation.code.SharpSAT
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Structure.v1.Atlas.TheoryOfComputation.code.SharpSATInIP.Part2


namespace SharpSATInIP

open InteractiveProofs NPCompleteness TuringMachine

/--
The univariate polynomial that the honest prover sends in round `i` of the
sum-check protocol, evaluated at point `z`: with the first `i` variables fixed
to the previously chosen field challenges, variable `x_i` set to `z`, sum over
all Boolean assignments of the remaining `m - i - 1` variables of `arithEval φ`.
-/
noncomputable def arithPartialSum {q : ℕ} [NeZero q]
    (φ : BoolFormula) (m : ℕ) (challenges : ℕ → ZMod q)
    (i : ℕ) (z : ZMod q) : ZMod q :=
  if _h : i < m then
    Finset.sum (Finset.univ : Finset (Fin (m - i - 1) → Bool))
      (fun σ => φ.arithEval (fun j =>
        if j < i then challenges j
        else if j = i then z
        else if h2 : j - i - 1 < m - i - 1 then
          if σ ⟨j - i - 1, h2⟩ then 1 else 0
        else 0))
  else 0

/--
The verifier in the sum-check protocol for `#SAT`. In each of the `m` rounds it
extracts random field-element challenges from its coin tape and sends them to
the prover. After all rounds it checks (i) that each prover-message triple
`(v₀, v₁, v_r)` satisfies `v₀ + v₁ = ` previously claimed value, and (ii) that
the final claim equals `arithEval φ` at the chosen random point.
-/
noncomputable def sumCheckVerifier {Γ : Type} (enc : SumCheckEncoding Γ) :
    Verifier Unit Γ where
  sendMessage := fun w n coins transcript =>
    match enc.toSharpSATEncoding.decode w with
    | none => []
    | some (φ, _) =>
      let m := φ.numVars
      let roundIdx := transcript.length / 2
      if _h : roundIdx < m then

        let startBit := roundIdx * enc.bitsPerField
        let bits : Fin enc.bitsPerField → Bool := fun j =>
          if h2 : startBit + j.val < n then coins ⟨startBit + j.val, h2⟩ else false
        enc.encodeField (enc.coinsToField bits)
      else []
  decide := fun w n coins transcript =>
    match enc.toSharpSATEncoding.decode w with
    | none => false
    | some (φ, k) =>
      haveI := enc.hq_ne
      let m := φ.numVars
      if transcript.length ≠ 2 * m then false
      else

        let getChallenge : ℕ → ZMod enc.q := fun i =>
          let startBit := i * enc.bitsPerField
          let bits : Fin enc.bitsPerField → Bool := fun j =>
            if h2 : startBit + j.val < n then coins ⟨startBit + j.val, h2⟩ else false
          enc.coinsToField bits

        let getProverMsg : ℕ → Option (ZMod enc.q × ZMod enc.q × ZMod enc.q) := fun i =>
          match transcript[2 * i + 1]? with
          | none => none
          | some msg => enc.decodeTriple msg


        let result := List.range m |>.foldl (fun acc i =>
          match acc with
          | none => none
          | some claimedVal =>
            match getProverMsg i with
            | none => none
            | some (v0, v1, vr) =>
              if v0 + v1 = claimedVal then some vr
              else none)
          (some (k : ZMod enc.q))
        match result with
        | none => false
        | some finalClaimed =>


          let finalEval := φ.arithEval (fun j =>
            if j < m then getChallenge j else 0)
          finalClaimed == finalEval

/--
The honest prover for the sum-check protocol on `#SAT`. In round `i` it sends
the triple `(v₀, v₁, v_r)` where `v_b = Σ_{x_{i+1},…,x_{m-1}} arithEval φ` with
`x_0,…,x_{i-1}` set to past challenges and `x_i = b` (or `b = r`, the current
verifier challenge).
-/
noncomputable def sumCheckHonestProver {Γ : Type} (enc : SumCheckEncoding Γ) :
    Prover Γ :=
  fun w transcript =>
    match enc.toSharpSATEncoding.decode w with
    | none => []
    | some (φ, _) =>
      haveI := enc.hq_ne
      let m := φ.numVars
      let roundIdx := transcript.length / 2
      if roundIdx ≥ m then [] else

      let getChallenge : ℕ → ZMod enc.q := fun j =>
        match transcript[2 * j]? with
        | none => 0
        | some msg => match enc.decodeField msg with
          | some r => r
          | none => 0
      let currentR : ZMod enc.q := getChallenge roundIdx

      let v0 := arithPartialSum φ m getChallenge roundIdx 0
      let v1 := arithPartialSum φ m getChallenge roundIdx 1
      let vr := arithPartialSum φ m getChallenge roundIdx currentR
      enc.encodeTriple v0 v1 vr

end SharpSATInIP
