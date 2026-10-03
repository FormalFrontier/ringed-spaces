/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import RingedSpaces
public import RingedSpacesTests.RingedSpaceBaseChange

/-! # Public clients of full ringed-module square pasting -/

set_option warningAsError true

@[expose] public section

namespace Test.RingedSpaceBaseChangePasting

open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open RingedSpaces.Modules.PullbackCoherence RingedSpaces.Modules.BaseChange

universe u

variable {W₀ W₁ W₂ Z₀ Z₁ Z₂ : RingedSpace.{u, u}}

theorem client_pastePullback (a₀₁ : W₀ ⟶ W₁) (a₁₂ : W₁ ⟶ W₂)
    (v₀ : W₀ ⟶ Z₀) (v₁ : W₁ ⟶ Z₁) (v₂ : W₂ ⟶ Z₂)
    (b₀₁ : Z₀ ⟶ Z₁) (b₁₂ : Z₁ ⟶ Z₂)
    (h₀₁ : a₀₁ ≫ v₁ = v₀ ≫ b₀₁) (h₁₂ : a₁₂ ≫ v₂ = v₁ ≫ b₁₂) :
    pushPull (a₀₁ ≫ a₁₂) v₀ v₂ (b₀₁ ≫ b₁₂)
        (by rw [Category.assoc, h₁₂, ← Category.assoc, h₀₁, Category.assoc]) =
      (isoWhiskerLeft (R v₂) (pullbackComp b₀₁ b₁₂)).inv ≫
      (associator (R v₂) (L b₁₂) (L b₀₁)).inv ≫
      whiskerRight (pushPull a₁₂ v₁ v₂ b₁₂ h₁₂) (L b₀₁) ≫
      (associator (L a₁₂) (R v₁) (L b₀₁)).hom ≫
      whiskerLeft (L a₁₂) (pushPull a₀₁ v₀ v₁ b₀₁ h₀₁) ≫
      (associator (L a₁₂) (L a₀₁) (R v₀)).inv ≫
      (isoWhiskerRight (pullbackComp a₀₁ a₁₂) (R v₀)).hom :=
  pushPull_pastePullback a₀₁ a₁₂ v₀ v₁ v₂ b₀₁ b₁₂ h₀₁ h₁₂

variable {X₀ X₁ X₂ : RingedSpace.{u, u}}

theorem client_pastePushforward (a₀ : W₀ ⟶ X₀) (a₁ : W₁ ⟶ X₁) (a₂ : W₂ ⟶ X₂)
    (v₀ : W₀ ⟶ W₁) (v₁ : W₁ ⟶ W₂) (w₀ : X₀ ⟶ X₁) (w₁ : X₁ ⟶ X₂)
    (h₀ : a₀ ≫ w₀ = v₀ ≫ a₁) (h₁ : a₁ ≫ w₁ = v₁ ≫ a₂) :
    pushPull a₀ (v₀ ≫ v₁) (w₀ ≫ w₁) a₂
        (by
          calc
            a₀ ≫ (w₀ ≫ w₁) = (a₀ ≫ w₀) ≫ w₁ := (Category.assoc _ _ _).symm
            _ = (v₀ ≫ a₁) ≫ w₁ := by rw [h₀]
            _ = v₀ ≫ (a₁ ≫ w₁) := Category.assoc _ _ _
            _ = v₀ ≫ (v₁ ≫ a₂) := by rw [h₁]
            _ = (v₀ ≫ v₁) ≫ a₂ := (Category.assoc _ _ _).symm) =
      (isoWhiskerRight (pushforwardComp w₀ w₁) (L a₂)).inv ≫
      (associator (R w₀) (R w₁) (L a₂)).hom ≫
      whiskerLeft (R w₀) (pushPull a₁ v₁ w₁ a₂ h₁) ≫
      (associator (R w₀) (L a₁) (R v₁)).inv ≫
      whiskerRight (pushPull a₀ v₀ w₀ a₁ h₀) (R v₁) ≫
      (associator (L a₀) (R v₀) (R v₁)).hom ≫
      (isoWhiskerLeft (L a₀) (pushforwardComp v₀ v₁)).hom :=
  pushPull_pastePushforward a₀ a₁ a₂ v₀ v₁ w₀ w₁ h₀ h₁

open Test.RingedSpaceBaseChange in
theorem client_nonCartesian_pastePullback :
    pushPull (cornerMap ≫ 𝟙 pointRinged) cornerMap (𝟙 pointRinged)
      ((𝟙 pointRinged) ≫ (𝟙 pointRinged)) (by simp) =
    (isoWhiskerLeft (R (𝟙 pointRinged))
      (pullbackComp (𝟙 pointRinged) (𝟙 pointRinged))).inv ≫
    (associator (R (𝟙 pointRinged)) (L (𝟙 pointRinged)) (L (𝟙 pointRinged))).inv ≫
    whiskerRight (pushPull (𝟙 pointRinged) (𝟙 pointRinged)
      (𝟙 pointRinged) (𝟙 pointRinged) (by simp)) (L (𝟙 pointRinged)) ≫
    (associator (L (𝟙 pointRinged)) (R (𝟙 pointRinged)) (L (𝟙 pointRinged))).hom ≫
    whiskerLeft (L (𝟙 pointRinged))
      (pushPull cornerMap cornerMap (𝟙 pointRinged) (𝟙 pointRinged) (by simp)) ≫
    (associator (L (𝟙 pointRinged)) (L cornerMap) (R cornerMap)).inv ≫
    (isoWhiskerRight (pullbackComp cornerMap (𝟙 pointRinged)) (R cornerMap)).hom :=
  pushPull_pastePullback cornerMap (𝟙 pointRinged) cornerMap
    (𝟙 pointRinged) (𝟙 pointRinged) (𝟙 pointRinged) (𝟙 pointRinged) (by simp) (by simp)

end Test.RingedSpaceBaseChangePasting
