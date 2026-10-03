/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

/-!
# Complex differentiability and smoothness on the complex line

On an open subset of `ℂ`, complex differentiability into a complete complex normed
space is equivalent to complex `C^∞` regularity. The index `∞` here denotes
smoothness, not the distinct analytic index `ω`.
-/

@[expose] public section

open scoped ContDiff Manifold

universe u

/-- For maps on the complex line with complete complex target, differentiability on an
open set is equivalent to complex smoothness on that set. -/
theorem contMDiffOn_iff_mdifferentiableOn_complex
    {F : Type u} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {f : ℂ → F} {s : Set ℂ} (hs : IsOpen s) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ, F) ∞ f s ↔
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ, F) f s := by
  rw [contMDiffOn_iff_contDiffOn, mdifferentiableOn_iff_differentiableOn]
  exact ⟨fun hf ↦ hf.differentiableOn (by norm_num), fun hf ↦ hf.contDiffOn hs⟩
