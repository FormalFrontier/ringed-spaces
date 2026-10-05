/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ComplexAnalysis.Analysis.Complex.FiniteDimensional
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

/-!
# Complex differentiability and smoothness in finite dimension

On an open subset of a finite-dimensional complex normed space, complex
differentiability into a complete complex normed space is equivalent to complex
`C^∞` regularity. The index `∞` denotes smoothness, not analytic index `ω`.

## References

* Formal Frontier, `ComplexAnalysis/Analysis/Complex/FiniteDimensional.lean`:
  `DifferentiableOn.analyticOnNhd_of_finiteDimensional`, the
  finite-dimensional complex differentiability-to-analyticity result used here.
* Mathlib, `Mathlib/Geometry/Manifold/ContMDiff/NormedSpace.lean`
  (Sébastien Gouëzel and Floris van Doorn):
  the model-space differentiability and manifold-regularity comparison.
* Ravi Vakil, *The Rising Sea: Foundations of Algebraic Geometry* (October 21, 2025
  draft), Definition 4.3.9 (p. 142): motivation for holomorphic local models,
  not a proof of this finite-dimensional complex-smoothness equivalence or an
  equivalence with real smoothness.
-/

@[expose] public section

open scoped ContDiff Manifold

universe u v

/-- On an open subset of a finite-dimensional complex normed space, manifold
smoothness with complete target is equivalent to complex differentiability.
The reverse implication uses Formal Frontier's finite-dimensional complex
analyticity theorem in `ComplexAnalysis.Analysis.Complex.FiniteDimensional`. -/
theorem contMDiffOn_iff_mdifferentiableOn_complex_of_finiteDimensional
    {E : Type u} {F : Type v} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] {f : E → F} {s : Set E} (hs : IsOpen s) :
    ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ f s ↔
      MDifferentiableOn 𝓘(ℂ, E) 𝓘(ℂ, F) f s := by
  rw [contMDiffOn_iff_contDiffOn, mdifferentiableOn_iff_differentiableOn]
  exact ⟨fun hf ↦ hf.differentiableOn (by norm_num),
    fun hf ↦ (hf.analyticOnNhd_of_finiteDimensional hs).contDiffOn_of_completeSpace⟩

/-- For maps on the complex line with complete complex target, differentiability on an
open set is equivalent to complex smoothness on that set. -/
theorem contMDiffOn_iff_mdifferentiableOn_complex
    {F : Type u} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {f : ℂ → F} {s : Set ℂ} (hs : IsOpen s) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ, F) ∞ f s ↔
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ, F) f s := by
  exact contMDiffOn_iff_mdifferentiableOn_complex_of_finiteDimensional hs
