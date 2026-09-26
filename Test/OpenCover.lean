/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import RingedSpaces.OpenCover

/-!
# Direct-import clients for ringed-space open-cover gluing

These clients use only the public API, without any access to the construction internals.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace Test.OpenCover

universe u

variable {X Y : RingedSpace.{u, u}} (C : RingedSpace.OpenCover X)

/-- Existence, actual restrictions, and uniqueness for an arbitrary full-morphism family. -/
theorem arbitraryFamily (f : ∀ i, C.obj i ⟶ Y)
    (hf : ∀ i j, pullback.fst (C.ι i) (C.ι j) ≫ f i =
      pullback.snd (C.ι i) (C.ι j) ≫ f j) :
    ∃! g : X ⟶ Y, ∀ i, C.ι i ≫ g = f i := by
  have restriction (i : C.J) : C.ι i ≫ C.glueMorphisms f hf = f i :=
    C.ι_glueMorphisms f hf i
  exact ⟨C.glueMorphisms f hf, restriction, fun g' hg' ↦
    C.hom_ext g' (C.glueMorphisms f hf) (fun i ↦ (hg' i).trans (restriction i).symm)⟩

/-- The empty family covers the empty restriction, even for an arbitrary ringed-space target. -/
def emptyCover (X : RingedSpace.{u, u}) :
    RingedSpace.OpenCover (X.restrict (Opens.isOpenEmbedding ⊥)) where
  J := ULift.{u} Empty
  U i := i.down.elim
  covers x := False.elim x.property

/-- The ordinary universal property applies to an empty indexed cover of an empty source. -/
theorem emptyFamily (X Y : RingedSpace.{u, u}) :
    ∃! g : X.restrict (Opens.isOpenEmbedding ⊥) ⟶ Y,
      ∀ i : (emptyCover X).J, (emptyCover X).ι i ≫ g = i.down.elim := by
  apply arbitraryFamily (emptyCover X) (fun i ↦ i.down.elim)
  intro i
  exact i.down.elim

/-- An infinite-indexed cover whose members away from zero are empty. -/
def infiniteCover (X : RingedSpace.{u, u}) : RingedSpace.OpenCover X where
  J := ULift.{u} ℕ
  U i := if i.down = 0 then ⊤ else ⊥
  covers _ := ⟨⟨0⟩, trivial⟩

/-- The same full-morphism gluing works for an infinite index type with empty members. -/
theorem infiniteFamily (X Y : RingedSpace.{u, u})
    (f : ∀ i, (infiniteCover X).obj i ⟶ Y)
    (hf : ∀ i j, pullback.fst ((infiniteCover X).ι i) ((infiniteCover X).ι j) ≫ f i =
      pullback.snd ((infiniteCover X).ι i) ((infiniteCover X).ι j) ≫ f j) :
    ∃! g : X ⟶ Y, ∀ i, (infiniteCover X).ι i ≫ g = f i :=
  arbitraryFamily (infiniteCover X) f hf

end Test.OpenCover
