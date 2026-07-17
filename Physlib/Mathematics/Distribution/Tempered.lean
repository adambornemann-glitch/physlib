/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
module

public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.Distribution.TemperedDistribution
/-!

# The embedding of `Lp` into tempered distributions

## i. Overview

Mathlib provides the linear embedding `MeasureTheory.Lp.toTemperedDistribution` of `Lp`
classes into tempered distributions, for a measure of temperate growth. In this module we
record the basic API for this embedding in the plain-function spelling used downstream: it
is injective, additive and commutes with scalar multiplication, and, for a symbol `g` of
temperate growth, the distributional identity `g · φ = u` (via `smulLeftCLM`) holds iff the
pointwise product `g • φ` is almost everywhere equal to `u`.

## ii. Key results

- `MeasureTheory.Lp.toTemperedDistribution_injective` : the embedding `Lp → 𝓢'` is injective.
- `MeasureTheory.Lp.smulLeftCLM_toTemperedDistribution_eq_iff` : the distributional identity
  `g · φ = u` (via `smulLeftCLM`) holds iff `g • ⇑φ =ᵐ ⇑u` pointwise a.e.
  (forward direction: `MeasureTheory.Lp.smul_coeFn_ae_eq_of_smulLeftCLM_eq`).

## iii. Table of contents

- A. Linearity and injectivity of the embedding
- B. Multiplication by temperate-growth symbols

## iv. References

-/

@[expose] public section

namespace MeasureTheory
namespace Lp

open TemperedDistribution
open scoped SchwartzMap ENNReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℂ F] [CompleteSpace F] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
  [μ.HasTemperateGrowth] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-!
## A. Linearity and injectivity of the embedding
-/

/-- The embedding of `Lp` into tempered distributions is injective. -/
lemma toTemperedDistribution_injective [FiniteDimensional ℝ E] [IsLocallyFiniteMeasure μ] :
    Function.Injective (toTemperedDistribution (E := E) (F := F) (p := p) (μ := μ)) :=
  LinearMap.ker_eq_bot.mp ker_toTemperedDistributionCLM_eq_bot

/- The next three lemmas restate `map_add`/`map_smul`/`map_zero` of
`toTemperedDistributionCLM` in the plain-function spelling `Lp.toTemperedDistribution` used
by downstream statements; the composed-CLM form does not match it syntactically. -/

/-- The embedding `Lp → 𝓢'` is additive. -/
@[simp]
lemma toTemperedDistribution_add (ψ φ : Lp F p μ) :
    toTemperedDistribution (ψ + φ) = toTemperedDistribution ψ + toTemperedDistribution φ :=
  map_add (toTemperedDistributionCLM F μ p) ψ φ

/-- The embedding `Lp → 𝓢'` commutes with scalar multiplication. -/
@[simp]
lemma toTemperedDistribution_smul (c : ℂ) (ψ : Lp F p μ) :
    toTemperedDistribution (c • ψ) = c • toTemperedDistribution ψ :=
  map_smul (toTemperedDistributionCLM F μ p) c ψ

/-- The embedding `Lp → 𝓢'` sends zero to zero. -/
@[simp]
lemma toTemperedDistribution_zero :
    toTemperedDistribution (0 : Lp F p μ) = 0 :=
  map_zero (toTemperedDistributionCLM F μ p)

/-!
## B. Multiplication by temperate-growth symbols
-/

variable [FiniteDimensional ℝ E] [IsLocallyFiniteMeasure μ]

/-- If multiplication by a temperate-growth symbol `g` sends the tempered distribution of
`φ ∈ Lp` to (the distribution of) `u ∈ Lp`, then the pointwise product `g • φ` is almost
everywhere equal to `u` — in particular it lies in the same `Lp` space.

The hypothesis `hg` is load-bearing for the truth of the statement, not only for the proof:
for `g` without temperate growth, `smulLeftCLM` takes its junk value `0`, the hypothesis `h`
then forces `u = 0`, and the conclusion fails whenever `g • ⇑φ` is not a.e. zero. -/
lemma smul_coeFn_ae_eq_of_smulLeftCLM_eq {g : E → ℂ} (hg : g.HasTemperateGrowth)
    {φ u : Lp ℂ p μ}
    (h : smulLeftCLM ℂ g (toTemperedDistribution φ) = toTemperedDistribution u) :
    g • (φ : E → ℂ) =ᵐ[μ] u := by
  have hloc : LocallyIntegrable (g • (φ : E → ℂ)) μ :=
    locallyIntegrableOn_univ.mp <| .continuousOn_smul isOpen_univ.isLocallyClosed
      (((Lp.memLp φ).locallyIntegrable Fact.out).locallyIntegrableOn _)
      hg.1.continuous.continuousOn
  refine ae_eq_of_integral_contDiff_smul_eq hloc
    ((Lp.memLp u).locallyIntegrable Fact.out) fun t ht_diff ht_supp => ?_
  set T : 𝓢(E, ℂ) :=
    (ht_supp.comp_left (g := Complex.ofRealCLM) rfl).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp ht_diff) with hT
  have hT_apply : ∀ x, T x = (t x : ℂ) := fun x => by simp only [hT]; rfl
  have htest := DFunLike.congr_fun h T
  rw [smulLeftCLM_apply_apply, toTemperedDistribution_apply, toTemperedDistribution_apply]
    at htest
  calc ∫ x, t x • (g • (φ : E → ℂ)) x ∂μ
      = ∫ x, SchwartzMap.smulLeftCLM ℂ g T x • (φ : E → ℂ) x ∂μ := by
        apply integral_congr_ae
        filter_upwards with x
        simp only [SchwartzMap.smulLeftCLM_apply_apply hg, hT_apply, Pi.smul_apply', smul_eq_mul,
          Complex.real_smul]
        ring
    _ = ∫ x, T x • (u : E → ℂ) x ∂μ := htest
    _ = ∫ x, t x • (u : E → ℂ) x ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      simp only [hT_apply, Complex.real_smul, smul_eq_mul]

/-- The distributional identity `g · φ = u` (via `smulLeftCLM`) holds iff the pointwise product
`g • φ` is almost everywhere equal to `u`. As in the forward direction
`smul_coeFn_ae_eq_of_smulLeftCLM_eq`, the temperate-growth hypothesis `hg` is load-bearing. -/
lemma smulLeftCLM_toTemperedDistribution_eq_iff {g : E → ℂ} (hg : g.HasTemperateGrowth)
    {φ u : Lp ℂ p μ} :
    smulLeftCLM ℂ g (toTemperedDistribution φ) = toTemperedDistribution u ↔
      g • (φ : E → ℂ) =ᵐ[μ] u := by
  refine ⟨smul_coeFn_ae_eq_of_smulLeftCLM_eq hg, fun h => ?_⟩
  refine DFunLike.ext _ _ fun T => ?_
  rw [smulLeftCLM_apply_apply, toTemperedDistribution_apply, toTemperedDistribution_apply]
  refine integral_congr_ae ?_
  filter_upwards [h] with x hx
  simp only [SchwartzMap.smulLeftCLM_apply_apply hg, Pi.smul_apply', smul_eq_mul] at hx ⊢
  rw [← hx]
  ring

end Lp
end MeasureTheory
