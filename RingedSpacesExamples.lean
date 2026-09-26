/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import RingedSpaces

/-!
# Aggregate-import examples for ringed spaces and module presheaves

These examples check gluing along arbitrary indexed open covers and literal
intersections, full inverse-image factorization, and inverse-image module
presheaf constructions through the public aggregate import.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open RingedSpaces.Modules.PresheafInverseImage

universe u v

example {X Y : RingedSpace.{u, u}} (C : RingedSpace.OpenCover X)
    (f : ∀ i, C.obj i ⟶ Y)
    (hf : ∀ i j, pullback.fst (C.ι i) (C.ι j) ≫ f i =
      pullback.snd (C.ι i) (C.ι j) ≫ f j) :
    ∃! global : X ⟶ Y, ∀ i, C.ι i ≫ global = f i :=
  C.existsUnique_gluing f hf

example {X Y : RingedSpace.{u, u}} (C : RingedSpace.OpenCover X)
    (f : ∀ i, C.obj i ⟶ Y)
    (hf : ∀ i j, RingedSpace.restrictMap (C.U i ⊓ C.U j) (C.U i)
        inf_le_left ≫ f i =
      RingedSpace.restrictMap (C.U i ⊓ C.U j) (C.U j)
        inf_le_right ≫ f j) :
    ∃! global : X ⟶ Y, ∀ i, C.ι i ≫ global = f i :=
  C.existsUnique_gluing_of_intersection f hf

noncomputable example {X Y : TopCat.{v}} (map : X ⟶ Y) (R : Y.Presheaf RingCat.{v}) :
    inverseImageFunctor map R ⊣
      PresheafOfModules.pushforward (F := Opens.map map)
        ((Opens.map map).op.pointwiseLeftKanExtensionUnit R) :=
  adjunction map R
