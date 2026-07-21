/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
module

public import Physlib.QuantumMechanics.HilbertSpaces.SpaceD.Fourier
public import Physlib.QuantumMechanics.Operators.Multiplication
public import Physlib.QuantumMechanics.Operators.SpectralTheory.SelfAdjoint
/-!

# Derivative operators

## i. Overview

Every constant-coefficient differential operator is, up to the Fourier transform, a multiplication
operator. In this module we take that as a definition: for a symbol `f : Space d → ℂ`, a function
of the wavenumber `k`, the derivative operator `derivOperator f` is the conjugate
`𝓕⁻¹ ∘ 𝓜 (f ∘ 2π•) ∘ 𝓕` of the multiplication operator by the Fourier unitary, through
`LinearPMap.unitaryConj`.

## ii. Key results

- `derivOperator` : the derivative operator with wavenumber symbol `f`.
- `derivOperator_hasDenseDomain` : it is densely defined for a.e.-strongly-measurable `f`.
- `derivOperator_adjoint` : its adjoint is the derivative operator of the conjugate symbol.
- `derivOperator_isSelfAdjoint` : it is self-adjoint for real-valued `f`.
- `schwartzSubmodule_le_derivOperator_domain` : the Schwartz submodule lies in the domain for
    temperate-growth `f`.

## iii. Table of contents

- A. The derivative operator
- B. The Schwartz submodule in the domain

## iv. References

-/

@[expose] public section

namespace QuantumMechanics
namespace SpaceDHilbertSpace
noncomputable section

open MeasureTheory ComplexConjugate
open LinearPMap

/-!
## A. The derivative operator
-/

variable {d : ℕ} {f : Space d → ℂ}

/-- The derivative operator with symbol `f : Space d → ℂ`, a function of the wavenumber `k`. -/
def derivOperator (f : Space d → ℂ) : SpaceDHilbertSpace d →ₗ.[ℂ] SpaceDHilbertSpace d :=
  (𝓜 volume fun ξ => f ((2 * Real.pi) • ξ)).unitaryConj (fourierUnitary d).symm

/-- The wavenumber rescaling `ξ ↦ 2πξ` preserves a.e.-strong measurability of symbols:
nonzero scaling is quasi-measure-preserving for the Haar measure. -/
lemma aestronglyMeasurable_comp_two_pi_smul (hf : AEStronglyMeasurable f volume) :
    AEStronglyMeasurable (fun ξ : Space d => f ((2 * Real.pi) • ξ)) volume :=
  hf.comp_quasiMeasurePreserving
    ⟨measurable_const_smul _, by
      rw [Measure.map_addHaar_smul volume (by positivity)]
      exact Measure.smul_absolutelyContinuous⟩

/-- Membership: `ψ ∈ D(derivOperator f)` iff `𝓕ψ` lies in the domain of multiplication by the
rescaled symbol. -/
lemma mem_derivOperator_domain_iff {ψ : SpaceDHilbertSpace d} :
    ψ ∈ (derivOperator f).domain
      ↔ fourierUnitary d ψ ∈ (𝓜 volume fun ξ => f ((2 * Real.pi) • ξ)).domain := Iff.rfl

/-- The defining formula: `derivOperator f ψ = 𝓕⁻¹ ((f ∘ 2π•) · 𝓕ψ)`. -/
lemma derivOperator_apply (ψ : (derivOperator f).domain) :
    derivOperator f ψ = (fourierUnitary d).symm
      ((𝓜 volume fun ξ => f ((2 * Real.pi) • ξ))
        ⟨fourierUnitary d ↑ψ, mem_derivOperator_domain_iff.mp ψ.2⟩) := rfl

/-- The derivative operator is densely defined. -/
lemma derivOperator_hasDenseDomain (hf : AEStronglyMeasurable f volume) :
    (derivOperator f).HasDenseDomain :=
  (mulOperator_hasDenseDomain (aestronglyMeasurable_comp_two_pi_smul hf)).unitaryConj_dense_domain

/-- The adjoint of a derivative operator is the derivative operator of the conjugate symbol:
`(derivOperator f)† = derivOperator (conj ∘ f)`. -/
lemma derivOperator_adjoint (hf : AEStronglyMeasurable f volume) :
    (derivOperator f)† = derivOperator (conj ∘ f) := by
  rw [derivOperator, unitaryConj_adjoint _
      (mulOperator_hasDenseDomain (aestronglyMeasurable_comp_two_pi_smul hf)),
    mulOperator_adjoint_eq_conj (aestronglyMeasurable_comp_two_pi_smul hf)]
  rfl

/-- The derivative operator of a real-valued symbol is self-adjoint on its maximal domain. -/
lemma derivOperator_isSelfAdjoint (hf : AEStronglyMeasurable f volume)
    (hf' : conj ∘ f = f) : IsSelfAdjoint (derivOperator f) :=
  LinearPMap.unitaryConj_isSelfAdjoint (fourierUnitary d).symm
    (mulOperator_isSelfAdjoint_ofReal (aestronglyMeasurable_comp_two_pi_smul hf)
      (funext fun ξ => congrFun hf' ((2 * Real.pi) • ξ)))

/-!
## B. The Schwartz submodule in the domain
-/

/-- For a temperate-growth symbol the Schwartz submodule lies in the domain of the derivative
operator. -/
lemma schwartzSubmodule_le_derivOperator_domain (hf : f.HasTemperateGrowth) :
    SchwartzSubmodule d ≤ (derivOperator f).domain :=
  fun _ hψ => mem_derivOperator_domain_iff.mpr
    (mulOperator_domain_ge_of_hasTemperateGrowth (by fun_prop) volume
      (fourierUnitary_map_schwartzSubmodule ▸ Submodule.mem_map_of_mem hψ))

end
end SpaceDHilbertSpace
end QuantumMechanics
