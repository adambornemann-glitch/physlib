/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
module

public import Mathlib.Analysis.Distribution.Sobolev
public import Physlib.Mathematics.Distribution.Tempered
public import Physlib.QuantumMechanics.HilbertSpaces.SpaceD.SchwartzSubmodule
/-!

# Sobolev submodules of `SpaceDHilbertSpace`

## i. Overview

In this module we define the Sobolev submodules of `SpaceDHilbertSpace`.

## ii. Key results

- `sobolevSubmodule d s` : the Sobolev space `H^s` as a submodule of `SpaceDHilbertSpace d`.
- `schwartzIncl_mem_sobolevSubmodule` / `schwartzSubmodule_le_sobolevSubmodule` /
    `sobolevSubmodule_dense` : Schwartz maps lie in every `H^s`, which is therefore dense.
- `sobolevSubmodule_antitone` : `H^s ≤ H^s'` for `s' ≤ s`.

## iii. Table of contents

- A. The Sobolev submodule `H^s`

## iv. References

-/

@[expose] public section

namespace QuantumMechanics
namespace SpaceDHilbertSpace

open MeasureTheory TemperedDistribution
open scoped SchwartzMap

variable {d : ℕ}

/-!
## A. The Sobolev submodule `H^s`
-/

/-- The **Sobolev space** `H^s` as a submodule of `SpaceDHilbertSpace d`: the L² classes whose
associated tempered distribution satisfies `MemSobolev s 2`. -/
def sobolevSubmodule (d : ℕ) (s : ℝ) : Submodule ℂ (SpaceDHilbertSpace d) where
  carrier := {ψ | MemSobolev s 2 (Lp.toTemperedDistribution ψ)}
  add_mem' {ψ φ} hψ hφ := by simpa [Lp.toTemperedDistribution_add] using hψ.add hφ
  zero_mem' := by simp [Lp.toTemperedDistribution_zero]
  smul_mem' c ψ hψ := by simpa [Lp.toTemperedDistribution_smul] using hψ.smul c

/-- Membership in `H^s` is the Sobolev condition on the associated tempered distribution. -/
lemma mem_sobolevSubmodule_iff {s : ℝ} {ψ : SpaceDHilbertSpace d} :
    ψ ∈ sobolevSubmodule d s ↔ MemSobolev s 2 (Lp.toTemperedDistribution ψ) := Iff.rfl

/-- Schwartz maps lie in every Sobolev space `H^s`. -/
lemma schwartzIncl_mem_sobolevSubmodule (s : ℝ) (g : 𝓢(Space d, ℂ)) :
    (schwartzIncl volume g : SpaceDHilbertSpace d) ∈ sobolevSubmodule d s := by
  rw [mem_sobolevSubmodule_iff, schwartzIncl_apply, Lp.toTemperedDistribution_toLp_eq]
  exact g.memSobolev

/-- The Schwartz submodule is contained in every Sobolev space `H^s`. -/
lemma schwartzSubmodule_le_sobolevSubmodule (s : ℝ) :
    SchwartzSubmodule d ≤ sobolevSubmodule d s := by
  rintro ψ ⟨g, rfl⟩
  exact schwartzIncl_mem_sobolevSubmodule s g

/-- Every Sobolev space `H^s` is dense in `SpaceDHilbertSpace d`, containing the dense Schwartz
submodule. -/
lemma sobolevSubmodule_dense (s : ℝ) :
    Dense (sobolevSubmodule d s : Set (SpaceDHilbertSpace d)) :=
  (SchwartzSubmodule.dense d volume).mono (schwartzSubmodule_le_sobolevSubmodule s)

/-- The Sobolev spaces shrink as the regularity index grows: `H^s ≤ H^s'` for `s' ≤ s`. -/
lemma sobolevSubmodule_antitone (d : ℕ) : Antitone (sobolevSubmodule d) :=
  fun _ _ h _ hψ => hψ.mono h

end SpaceDHilbertSpace

end QuantumMechanics
