/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import RingedSpaces

/-! # Aggregate-import clients for inverse-image module-presheaf Hom -/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open RingedSpaces.Modules.PresheafInverseImage

namespace Test.PresheafInverseImageHomRoot

universe v

variable {X Y : TopCat.{v}} (f : X ⟶ Y) (R : Y.Presheaf RingCat.{v})
  (M : PresheafOfModules.{v} R)
  (N : PresheafOfModules.{v} ((Opens.map f).op.pointwiseLeftKanExtension R))

theorem completeHomEquivalence
    (g : (inverseImageFunctor f R).obj M ⟶ N) :
    backward f R (forward f R g) = g :=
  (homEquiv f R M N).left_inv g

/-- The ordinary aggregate import provides the inverse-image/pushforward adjunction. -/
noncomputable def actualAdjunction : inverseImageFunctor f R ⊣
    PresheafOfModules.pushforward (F := Opens.map f)
      ((Opens.map f).op.pointwiseLeftKanExtensionUnit R) :=
  adjunction f R

theorem additiveComparison
    (g : (inverseImageFunctor f R).obj M ⟶ N) :
    (PresheafOfModules.toPresheaf R).map (forward f R g) ≫
      ((PresheafOfModules.pushforwardCompToPresheaf (F := Opens.map f)
        ((Opens.map f).op.pointwiseLeftKanExtensionUnit R)).app N).hom =
    (TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat.{v} f).homEquiv
      M.presheaf N.presheaf
      ((underlyingComparison f R).inv.app M ≫
        (PresheafOfModules.toPresheaf _).map g) :=
  forward_underlying_additive f R g

end Test.PresheafInverseImageHomRoot
