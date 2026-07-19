/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Physlib.Mathematics.Resolvent
/-!

# The Schwartz resolvent multiplier

## i. Overview

For a normed space `E`, a continuous linear functional `L : E →L[ℝ] ℝ`, and `z : ℂ` with `z.im ≠ 0`,
multiplication by the affine symbol `ξ ↦ z + a·L(ξ)` is a surjection of the Schwartz space
`𝓢(E, ℂ)`, with multiplication by the reciprocal symbol as a right inverse.

## ii. Key results

- `resolventMulCLM` / `resolventMulInvCLM` : multiplication by the affine symbol and its reciprocal.
- `hasTemperateGrowth_resolventMul_inv` : the reciprocal symbol has temperate growth.
- `resolventMulCLM_comp_inv` / `resolventMulInvCLM_comp` : the two multipliers are mutually inverse.
- `resolventMulCLE` : the affine multiplier as a continuous linear equivalence of `𝓢(E, ℂ)`.
- `resolventMulCLM_surjective` / `resolventMulCLM_bijective` : multiplication by the affine symbol
    is a bijection of `𝓢(E, ℂ)`.

## iii. Table of contents

- A. Temperate growth of the symbols
- B. Bijectivity of the Schwartz multiplier

## iv. References

-/

@[expose] public section

open Function SchwartzMap

namespace Physlib.Resolvent

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {z : ℂ}

/-!
## A. Temperate growth of the symbols
-/

/-- The affine symbol `z + a·t` never vanishes for non-real `z`. -/
lemma resolventMul_ne_zero (hz : z.im ≠ 0) (a t : ℝ) : z + (a : ℂ) * (t : ℂ) ≠ 0 :=
  fun h ↦ hz (by simpa using congrArg Complex.im h)

/-- The reciprocal symbol `ξ ↦ (z + a·L(ξ))⁻¹` has temperate growth: it is the resolvent of `-z`
composed with the temperate map `ξ ↦ a·L(ξ)`. -/
lemma hasTemperateGrowth_resolventMul_inv (L : E →L[ℝ] ℝ) (a : ℝ) (hz : z.im ≠ 0) :
    Function.HasTemperateGrowth (fun ξ : E => (z + (a : ℂ) * (L ξ : ℝ))⁻¹) := by
  have hz' : (-z).im ≠ 0 := by simpa using hz
  have heq : (fun ξ : E => (z + (a : ℂ) * (L ξ : ℝ))⁻¹)
      = resolvent (R := ℝ) (-z) ∘ fun ξ : E => a * L ξ := by
    funext ξ
    simp only [Function.comp_apply, resolvent, Ring.inverse_eq_inv, Complex.coe_algebraMap,
      Complex.ofReal_mul, sub_neg_eq_add, inv_inj]
    ring
  rw [heq]
  exact (hasTemperateGrowth_resolvent hz').comp
    ((Function.HasTemperateGrowth.const a).mul L.hasTemperateGrowth)

/-!
## B. Bijectivity of the Schwartz multiplier
-/

/-- The Schwartz multiplier by the affine resolvent symbol `ξ ↦ z + a·L(ξ)`. -/
noncomputable def resolventMulCLM (L : E →L[ℝ] ℝ) (a : ℝ) (z : ℂ) :
    𝓢(E, ℂ) →L[ℂ] 𝓢(E, ℂ) := smulLeftCLM ℂ (fun ξ : E => z + (a : ℂ) * (L ξ : ℝ))

/-- The Schwartz multiplier by the reciprocal resolvent symbol `ξ ↦ (z + a·L(ξ))⁻¹`.
**Junk value**
For `z.im = 0` (and `a ≠ 0`, `L ≠ 0`) the reciprocal symbol has a pole and is not temperate, so
`smulLeftCLM`'s junk branch makes this the zero operator. All lemmas about it assume  `z.im ≠ 0`. -/
noncomputable def resolventMulInvCLM (L : E →L[ℝ] ℝ) (a : ℝ) (z : ℂ) :
    𝓢(E, ℂ) →L[ℂ] 𝓢(E, ℂ) := smulLeftCLM ℂ (fun ξ : E => (z + (a : ℂ) * (L ξ : ℝ))⁻¹)

/-- The affine multiplier composed with the reciprocal multiplier is the identity on `𝓢(E, ℂ)`:
multiplying by the reciprocal symbol and then by the affine symbol restores the original map. -/
@[simp]
lemma resolventMulCLM_comp_inv (L : E →L[ℝ] ℝ) (a : ℝ) (hz : z.im ≠ 0) :
    resolventMulCLM L a z ∘L resolventMulInvCLM L a z = ContinuousLinearMap.id ℂ 𝓢(E, ℂ) := by
  have hcancel : (fun ξ : E => z + (a : ℂ) * (L ξ : ℝ)) * (fun ξ => (z + (a : ℂ) * (L ξ : ℝ))⁻¹)
      = fun _ => (1 : ℂ) :=
    funext fun ξ => mul_inv_cancel₀ (resolventMul_ne_zero hz a _)
  simp only [resolventMulCLM, resolventMulInvCLM]
  rw [smulLeftCLM_compL_smulLeftCLM (by fun_prop) (hasTemperateGrowth_resolventMul_inv L a hz),
    hcancel, smulLeftCLM_const, one_smul]

/-- The reciprocal multiplier composed with the affine multiplier is the identity. -/
@[simp]
lemma resolventMulInvCLM_comp (L : E →L[ℝ] ℝ) (a : ℝ) (hz : z.im ≠ 0) :
    resolventMulInvCLM L a z ∘L resolventMulCLM L a z = ContinuousLinearMap.id ℂ 𝓢(E, ℂ) := by
  have hcancel : (fun ξ : E => (z + (a : ℂ) * (L ξ : ℝ))⁻¹) * (fun ξ => z + (a : ℂ) * (L ξ : ℝ))
      = fun _ => (1 : ℂ) :=
    funext fun ξ => inv_mul_cancel₀ (resolventMul_ne_zero hz a _)
  simp only [resolventMulCLM, resolventMulInvCLM]
  rw [smulLeftCLM_compL_smulLeftCLM (hasTemperateGrowth_resolventMul_inv L a hz) (by fun_prop),
    hcancel, smulLeftCLM_const, one_smul]

/-- For `z.im ≠ 0`, multiplication by the affine resolvent symbol as a continuous linear
equivalence of `𝓢(E, ℂ)`, with the reciprocal multiplier as inverse. -/
noncomputable def resolventMulCLE (L : E →L[ℝ] ℝ) (a : ℝ) (hz : z.im ≠ 0) :
    𝓢(E, ℂ) ≃L[ℂ] 𝓢(E, ℂ) :=
  ContinuousLinearEquiv.equivOfInverse (resolventMulCLM L a z) (resolventMulInvCLM L a z)
    (fun χ => by simpa using DFunLike.congr_fun (resolventMulInvCLM_comp L a hz) χ)
    (fun χ => by simpa using DFunLike.congr_fun (resolventMulCLM_comp_inv L a hz) χ)

@[simp]
lemma resolventMulCLE_apply (L : E →L[ℝ] ℝ) (a : ℝ) (hz : z.im ≠ 0) (χ : 𝓢(E, ℂ)) :
    resolventMulCLE L a hz χ = resolventMulCLM L a z χ := rfl

@[simp]
lemma resolventMulCLE_symm_apply (L : E →L[ℝ] ℝ) (a : ℝ) (hz : z.im ≠ 0) (χ : 𝓢(E, ℂ)) :
    (resolventMulCLE L a hz).symm χ = resolventMulInvCLM L a z χ := rfl

/-- For `z.im ≠ 0`, multiplication by the affine symbol `ξ ↦ z + a·L(ξ)` is surjective on `𝓢(E, ℂ)`;
a preimage of `χ` is obtained by multiplying `χ` by the reciprocal symbol. -/
lemma resolventMulCLM_surjective (L : E →L[ℝ] ℝ) (a : ℝ) (hz : z.im ≠ 0) :
    Function.Surjective (resolventMulCLM L a z) := (resolventMulCLE L a hz).surjective

/-- Multiplication by the affine symbol is a bijection of `𝓢(E, ℂ)`. -/
lemma resolventMulCLM_bijective (L : E →L[ℝ] ℝ) (a : ℝ) (hz : z.im ≠ 0) :
    Function.Bijective (resolventMulCLM L a z) := (resolventMulCLE L a hz).bijective

end Physlib.Resolvent
