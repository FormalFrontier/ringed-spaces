/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import RingedSpaces
import Mathlib.Analysis.Calculus.Deriv.Abs

/-! Ordinary-import clients for backward finite-regularity scalar-function maps. -/

@[expose] public section

set_option warningAsError true

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open scoped ContDiff Manifold

noncomputable section

namespace FiniteRegularityFunctionsMapsTest

open FiniteRegularityFunctions

/-- A proper real open neighborhood of the image of zero under translation. -/
def targetOpen : Opens ℝ := ⟨Set.Iio (2 : ℝ), isOpen_Iio⟩

/-- The nonconstant real affine map used to pull back a `C¹` section. -/
def translation (point : ℝ) : ℝ := point + 1

private theorem translation_zero_mem : translation (0 : ℝ) ∈ targetOpen := by
  norm_num [targetOpen, translation]

example : translation 0 ≠ translation 1 := by
  norm_num [translation]

private theorem translation_contMDiff :
    ContMDiff 𝓘(ℝ) 𝓘(ℝ) (↑(1 : ℕ) : ℕ∞ω) translation := by
  have h : ContMDiff 𝓘(ℝ) 𝓘(ℝ) (↑(1 : ℕ) : ℕ∞ω)
      ((id : ℝ → ℝ) + fun _ => 1) := contMDiff_id.add contMDiff_const
  have heq : ((id : ℝ → ℝ) + fun _ => 1) = translation := by
    funext point
    rfl
  exact heq ▸ h

private theorem translation_contMDiff_smooth :
    ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ translation := by
  have h : ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞
      ((id : ℝ → ℝ) + fun _ => 1) := contMDiff_id.add contMDiff_const
  have heq : ((id : ℝ → ℝ) + fun _ => 1) = translation := by
    funext point
    rfl
  exact heq ▸ h

/-- A second nonconstant translation for composing real maps. -/
def secondTranslation (point : ℝ) : ℝ := point + 2

private theorem secondTranslation_contMDiff :
    ContMDiff 𝓘(ℝ) 𝓘(ℝ) (↑(1 : ℕ) : ℕ∞ω) secondTranslation := by
  have h : ContMDiff 𝓘(ℝ) 𝓘(ℝ) (↑(1 : ℕ) : ℕ∞ω)
      ((id : ℝ → ℝ) + fun _ => 2) := contMDiff_id.add contMDiff_const
  have heq : ((id : ℝ → ℝ) + fun _ => 2) = secondTranslation := by
    funext point
    rfl
  exact heq ▸ h

example : secondTranslation 0 ≠ secondTranslation 1 := by
  norm_num [secondTranslation]

example : locallyRingedSpaceMap 𝓘(ℝ) 𝓘(ℝ) ℝ ℝ 1 id contMDiff_id =
    𝟙 (locallyRingedSpace 1 𝓘(ℝ) ℝ) :=
  locallyRingedSpaceMap_id 𝓘(ℝ) ℝ 1

example : locallyRingedSpaceMap 𝓘(ℝ) 𝓘(ℝ) ℝ ℝ 1
      (secondTranslation ∘ translation)
      (secondTranslation_contMDiff.comp translation_contMDiff) =
    locallyRingedSpaceMap 𝓘(ℝ) 𝓘(ℝ) ℝ ℝ 1 translation
        translation_contMDiff ≫
      locallyRingedSpaceMap 𝓘(ℝ) 𝓘(ℝ) ℝ ℝ 1 secondTranslation
        secondTranslation_contMDiff :=
  locallyRingedSpaceMap_comp 𝓘(ℝ) 𝓘(ℝ) ℝ ℝ 𝓘(ℝ) ℝ 1
    translation secondTranslation translation_contMDiff secondTranslation_contMDiff

example : (locallyRingedSpaceMap 𝓘(ℝ) 𝓘(ℝ) ℝ ℝ 1 translation
      translation_contMDiff).stalkMap (0 : ℝ) ≫ evalHom 𝓘(ℝ) ℝ 1 0 =
    evalHom 𝓘(ℝ) ℝ 1 (translation 0) :=
  stalkMap_evalHom 𝓘(ℝ) 𝓘(ℝ) ℝ ℝ 1 translation translation_contMDiff 0

example : IsLocalHom ((locallyRingedSpaceMap 𝓘(ℝ) 𝓘(ℝ) ℝ ℝ 1 translation
      translation_contMDiff).stalkMap (0 : ℝ)).hom :=
  stalkMap_isLocalHom 𝓘(ℝ) 𝓘(ℝ) ℝ ℝ 1 translation translation_contMDiff 0

private def coordinate : (sheaf 𝓘(ℝ) ℝ 1).presheaf.obj (op targetOpen) :=
  ofFunction (IM := 𝓘(ℝ)) (M := ℝ) 1 targetOpen
    (fun point => (point : ℝ)) contMDiff_subtype_val

example : (0 : ℝ) ∈ ContinuousFunctions.inverseImage ℝ ℝ translation
    translation_contMDiff.continuous targetOpen ∧ (1 : ℝ) ∈ targetOpen ∧
      (2 : ℝ) ∉ targetOpen := by
  constructor
  · change translation (0 : ℝ) ∈ targetOpen
    norm_num [translation, targetOpen]
  constructor <;> norm_num [targetOpen]

example : precompose 𝓘(ℝ) 𝓘(ℝ) ℝ ℝ 1 translation translation_contMDiff
    targetOpen coordinate
      (⟨0, by
        change translation (0 : ℝ) ∈ targetOpen
        exact translation_zero_mem⟩ :
        ContinuousFunctions.inverseImage ℝ ℝ translation
          translation_contMDiff.continuous targetOpen) = 1 := by
  rw [precompose_apply]
  change translation (0 : ℝ) = 1
  norm_num [translation]

example : (locallyRingedSpaceMap 𝓘(ℝ) 𝓘(ℝ) ℝ ℝ 1 translation
      translation_contMDiff).stalkMap (0 : ℝ)
        ((sheaf 𝓘(ℝ) ℝ 1).presheaf.germ targetOpen (translation (0 : ℝ))
          translation_zero_mem coordinate) =
      (sheaf 𝓘(ℝ) ℝ 1).presheaf.germ
        (ContinuousFunctions.inverseImage ℝ ℝ translation
          translation_contMDiff.continuous targetOpen) (0 : ℝ)
        (by
          change translation (0 : ℝ) ∈ targetOpen
          exact translation_zero_mem)
        (precompose 𝓘(ℝ) 𝓘(ℝ) ℝ ℝ 1 translation translation_contMDiff
          targetOpen coordinate) := by
  exact stalkMap_germ 𝓘(ℝ) 𝓘(ℝ) ℝ ℝ 1 translation translation_contMDiff
    targetOpen (0 : ℝ) translation_zero_mem coordinate

example : eval 𝓘(ℝ) ℝ 1 0
    ((locallyRingedSpaceMap 𝓘(ℝ) 𝓘(ℝ) ℝ ℝ 1 translation
      translation_contMDiff).stalkMap (0 : ℝ)
        ((sheaf 𝓘(ℝ) ℝ 1).presheaf.germ targetOpen (translation (0 : ℝ))
          translation_zero_mem coordinate)) = 1 := by
  have preimage_zero_mem : (0 : ℝ) ∈
      ContinuousFunctions.inverseImage ℝ ℝ translation
        translation_contMDiff.continuous targetOpen := by
    change translation (0 : ℝ) ∈ targetOpen
    exact translation_zero_mem
  rw [stalkMap_germ 𝓘(ℝ) 𝓘(ℝ) ℝ ℝ 1 translation translation_contMDiff
    targetOpen (0 : ℝ) translation_zero_mem coordinate]
  change eval 𝓘(ℝ) ℝ 1 0
    ((sheaf 𝓘(ℝ) ℝ 1).presheaf.germ
      (ContinuousFunctions.inverseImage ℝ ℝ translation
        translation_contMDiff.continuous targetOpen) (0 : ℝ)
      preimage_zero_mem
      (precompose 𝓘(ℝ) 𝓘(ℝ) ℝ ℝ 1 translation translation_contMDiff
        targetOpen coordinate)) = 1
  rw [eval_germ (IM := 𝓘(ℝ)) (M := ℝ) 1
    (ContinuousFunctions.inverseImage ℝ ℝ translation
      translation_contMDiff.continuous targetOpen) (0 : ℝ) preimage_zero_mem,
    precompose_apply]
  norm_num [coordinate, translation, ofFunction]

private theorem absolute_contMDiff_zero :
    ContMDiff 𝓘(ℝ) 𝓘(ℝ) (↑(0 : ℕ) : ℕ∞ω) (abs : ℝ → ℝ) := by
  simpa only [Nat.cast_zero] using
    (contMDiff_zero_iff.mpr continuous_abs :
      ContMDiff 𝓘(ℝ) 𝓘(ℝ) (0 : ℕ∞ω) (abs : ℝ → ℝ))

example : ¬ DifferentiableAt ℝ (abs : ℝ → ℝ) 0 :=
  not_differentiableAt_abs_zero

private def zeroCoordinate : (sheaf 𝓘(ℝ) ℝ 0).presheaf.obj (op targetOpen) :=
  ofFunction (IM := 𝓘(ℝ)) (M := ℝ) 0 targetOpen
    (fun point => (point : ℝ)) contMDiff_subtype_val

example : precompose 𝓘(ℝ) 𝓘(ℝ) ℝ ℝ 0 (abs : ℝ → ℝ)
    absolute_contMDiff_zero targetOpen zeroCoordinate
      (⟨0, by
        change |(0 : ℝ)| ∈ targetOpen
        norm_num [targetOpen]⟩ :
        ContinuousFunctions.inverseImage ℝ ℝ (abs : ℝ → ℝ)
          absolute_contMDiff_zero.continuous targetOpen) = 0 := by
  rw [precompose_apply]
  change |(0 : ℝ)| = 0
  norm_num

example : smoothToFinite (IM := 𝓘(ℝ)) (M := ℝ) 1 ≫
      sheafHom 𝓘(ℝ) 𝓘(ℝ) ℝ ℝ 1 translation
        (translation_contMDiff_smooth.of_le (by simp)) =
    translation_contMDiff_smooth.smoothSheafCommRingHom _ _ translation ≫
      (TopCat.Sheaf.pushforward _
        (TopCat.ofHom ⟨translation, translation_contMDiff_smooth.continuous⟩)).map
        (smoothToFinite (IM := 𝓘(ℝ)) (M := ℝ) 1) :=
  smoothToFinite_naturality 𝓘(ℝ) 𝓘(ℝ) ℝ ℝ 1 translation
    translation_contMDiff_smooth

example : (zeroSheafIso (IM := 𝓘(ℝ)) (M := ℝ)).hom ≫
      ContinuousFunctions.sheafHom ℝ ℝ ℝ (abs : ℝ → ℝ)
        absolute_contMDiff_zero.continuous =
    sheafHom 𝓘(ℝ) 𝓘(ℝ) ℝ ℝ 0 (abs : ℝ → ℝ) absolute_contMDiff_zero ≫
      (TopCat.Sheaf.pushforward _
        (TopCat.ofHom ⟨(abs : ℝ → ℝ), absolute_contMDiff_zero.continuous⟩)).map
        (zeroSheafIso (IM := 𝓘(ℝ)) (M := ℝ)).hom :=
  zeroSheafIso_naturality 𝓘(ℝ) 𝓘(ℝ) ℝ ℝ (abs : ℝ → ℝ) absolute_contMDiff_zero

example : LocallyRingedSpace := by
  letI : ChartedSpace ℝ PEmpty := ChartedSpace.empty ℝ PEmpty
  exact locallyRingedSpace 1 𝓘(ℝ) PEmpty

section EmptyDomain

private local instance : ChartedSpace ℝ PEmpty := ChartedSpace.empty ℝ PEmpty

example : locallyRingedSpace 1 𝓘(ℝ) PEmpty ⟶ locallyRingedSpace 1 𝓘(ℝ) ℝ := by
  let emptyMap : PEmpty → ℝ := fun point => point.elim
  have hempty : ContMDiff 𝓘(ℝ) 𝓘(ℝ) (↑(1 : ℕ) : ℕ∞ω) emptyMap := by
    intro point
    exact point.elim
  exact locallyRingedSpaceMap 𝓘(ℝ) 𝓘(ℝ) PEmpty ℝ 1 emptyMap hempty

end EmptyDomain

end FiniteRegularityFunctionsMapsTest
