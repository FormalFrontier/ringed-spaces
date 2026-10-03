/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import RingedSpaces

/-! Ordinary-import examples of finite-order scalar sections and their comparisons. -/

@[expose] public section

set_option warningAsError true

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open scoped ContDiff Manifold

noncomputable section

namespace FiniteRegularityFunctionsTest

open FiniteRegularityFunctions

private def constant (scalar : ℝ) :
    (sheaf 𝓘(ℝ) ℝ 1).presheaf.obj (op (⊤ : Opens ℝ)) :=
  ofFunction (IM := 𝓘(ℝ)) (M := ℝ) 1 ⊤ (fun _ ↦ scalar) contMDiff_const

private def identity : (sheaf 𝓘(ℝ) ℝ 1).presheaf.obj (op (⊤ : Opens ℝ)) :=
  ofFunction (IM := 𝓘(ℝ)) (M := ℝ) 1 ⊤ (fun point ↦ (point : ℝ))
    contMDiff_subtype_val

example (x : ℝ) :
    eval 𝓘(ℝ) ℝ 1 x
      ((sheaf 𝓘(ℝ) ℝ 1).presheaf.germ ⊤ x (by simp) (constant 2)) = 2 := by
  rw [eval_germ]
  rfl

example : IsUnit ((sheaf 𝓘(ℝ) ℝ 1).presheaf.germ ⊤ (0 : ℝ) (by simp)
    (constant 2)) := by
  rw [isUnit_stalk_iff, eval_germ]
  norm_num [constant, ofFunction]

example : ¬ IsUnit ((sheaf 𝓘(ℝ) ℝ 1).presheaf.germ ⊤ (0 : ℝ) (by simp)
    identity) := by
  rw [isUnit_stalk_iff, eval_germ]
  norm_num [identity, ofFunction]

private def smoothConstant :
    (smoothSheafCommRing 𝓘(ℝ) 𝓘(ℝ) ℝ ℝ).presheaf.obj (op (⊤ : Opens ℝ)) :=
  ⟨fun _ ↦ 2, contMDiff_const⟩

example (x : ℝ) :
    eval 𝓘(ℝ) ℝ 1 x
      ((sheaf 𝓘(ℝ) ℝ 1).presheaf.germ ⊤ x (by simp)
        ((smoothToFinite (IM := 𝓘(ℝ)) (M := ℝ) 1).hom.app (op (⊤ : Opens ℝ))
          smoothConstant)) = 2 := by
  rw [eval_germ, smoothToFinite_app, CommRingCat.ofHom_apply]
  rfl

/-- A proper real open set containing zero, used to test section restrictions. -/
def properOpen : Opens ℝ := ⟨Set.Iio (1 : ℝ), isOpen_Iio⟩

example : (0 : ℝ) ∈ properOpen ∧ (1 : ℝ) ∉ properOpen := by
  simp [properOpen]

private def globalAbsoluteContinuous :
    (ContinuousFunctions.sheaf ℝ ℝ).presheaf.obj (op (⊤ : Opens ℝ)) :=
  TopCat.ofHom ⟨fun point ↦ |(point : ℝ)|,
    continuous_abs.comp continuous_subtype_val⟩

private def globalAbsoluteZero :
    (sheaf 𝓘(ℝ) ℝ 0).presheaf.obj (op (⊤ : Opens ℝ)) :=
  continuousToZero (IM := 𝓘(ℝ)) (M := ℝ) ⊤ globalAbsoluteContinuous

private def restrictedAbsoluteZero :
    (sheaf 𝓘(ℝ) ℝ 0).presheaf.obj (op properOpen) :=
  restrict (IM := 𝓘(ℝ)) (M := ℝ) 0 (le_top : properOpen ≤ ⊤) globalAbsoluteZero

private def restrictedAbsoluteContinuous :
    (ContinuousFunctions.sheaf ℝ ℝ).presheaf.obj (op properOpen) :=
  (ContinuousFunctions.sheaf ℝ ℝ).presheaf.map
    (le_top : properOpen ≤ ⊤).hom.op globalAbsoluteContinuous

example : zeroToContinuous (IM := 𝓘(ℝ)) (M := ℝ) properOpen
    restrictedAbsoluteZero = restrictedAbsoluteContinuous := by
  calc
    _ = (ContinuousFunctions.sheaf ℝ ℝ).presheaf.map
        (le_top : properOpen ≤ ⊤).hom.op
          (zeroToContinuous (IM := 𝓘(ℝ)) (M := ℝ) ⊤ globalAbsoluteZero) := by
            simpa only [restrictedAbsoluteZero] using
              (zeroToContinuous_restrict (IM := 𝓘(ℝ)) (M := ℝ)
                (le_top : properOpen ≤ ⊤) globalAbsoluteZero).symm
    _ = restrictedAbsoluteContinuous := by
      rw [globalAbsoluteZero, zeroToContinuous_continuousToZero]
      rfl

example : continuousToZero (IM := 𝓘(ℝ)) (M := ℝ) properOpen
    restrictedAbsoluteContinuous = restrictedAbsoluteZero := by
  calc
    _ = restrict (IM := 𝓘(ℝ)) (M := ℝ) 0 (le_top : properOpen ≤ ⊤)
        (continuousToZero (IM := 𝓘(ℝ)) (M := ℝ) ⊤ globalAbsoluteContinuous) := by
          simpa only [restrictedAbsoluteContinuous] using
            (continuousToZero_restrict (IM := 𝓘(ℝ)) (M := ℝ)
              (le_top : properOpen ≤ ⊤) globalAbsoluteContinuous).symm
    _ = restrictedAbsoluteZero := rfl

private theorem restrictedAbsoluteZero_eval_zero : eval 𝓘(ℝ) ℝ 0 (0 : ℝ)
    ((sheaf 𝓘(ℝ) ℝ 0).presheaf.germ properOpen 0 (by simp [properOpen])
      restrictedAbsoluteZero) = 0 := by
  calc
    _ = restrictedAbsoluteZero ⟨0, by simp [properOpen]⟩ :=
      eval_germ (IM := 𝓘(ℝ)) (M := ℝ) 0 properOpen 0
        (by simp [properOpen]) restrictedAbsoluteZero
    _ = 0 := by
      rw [restrictedAbsoluteZero, restrict_apply, globalAbsoluteZero,
        continuousToZero_apply]
      change |(0 : ℝ)| = 0
      norm_num

example : ¬ IsUnit ((sheaf 𝓘(ℝ) ℝ 0).presheaf.germ properOpen 0
    (by simp [properOpen]) restrictedAbsoluteZero) := by
  rw [isUnit_stalk_iff, restrictedAbsoluteZero_eval_zero]
  simp

example : LocallyRingedSpace := by
  letI : ChartedSpace ℝ PEmpty := ChartedSpace.empty ℝ PEmpty
  exact locallyRingedSpace 0 𝓘(ℝ) PEmpty

end FiniteRegularityFunctionsTest
