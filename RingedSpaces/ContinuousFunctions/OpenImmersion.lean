/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Copyright (c) 2023 Heather Macbeth. All rights reserved.
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
The section comparison adapts the open-subtype argument of Heather Macbeth;
the continuous-function sheaf builds on work by Kim Morrison and collaborators.
-/
module

public import RingedSpaces.ContinuousFunctions
public import Mathlib.Geometry.RingedSpace.OpenImmersion

/-!
# Open immersions of continuous-function ringed spaces

An open embedding of topological spaces induces an open immersion for the actual
precomposition morphism of continuous-function ringed spaces over any topological
commutative ring. For T1 topological fields this also gives an open immersion
of locally ringed spaces and the intrinsic open-subtype restriction comparison.
All spaces and coefficients lie in one universe.

## References

* Mathlib, `Mathlib/Geometry/Manifold/Sheaf/LocallyRingedSpace.lean` (Heather Macbeth):
  the open-subtype comparison adapted for continuous-function sections.
* Mathlib, `Mathlib/Geometry/RingedSpace/OpenImmersion.lean` (Andrew Yang):
  the open-immersion API used for full ringed-space morphisms.
* Ravi Vakil, *The Rising Sea: Foundations of Algebraic Geometry* (21 October 2025
  draft), Definition 4.3.9 (p. 142): restricted versus intrinsic continuous
  real-function sheaves on a model ball motivate this comparison. The open
  immersion over any topological commutative ring is a project generalization;
  `T1Space` is used only for the field-valued locally ringed-space case.
-/

@[expose] public section

noncomputable section

open CategoryTheory TopologicalSpace Topology Opposite AlgebraicGeometry

universe u

namespace ContinuousFunctions

variable (U X : Type u) [TopologicalSpace U] [TopologicalSpace X]
variable (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

/-- On the image of each source open, the actual precomposition component of an open
embedding is an isomorphism for any topological commutative-ring coefficients. -/
theorem ringedSpaceMap_c_iso (j : U → X) (hj : IsOpenEmbedding j)
    (V : Opens U) :
    IsIso ((ringedSpaceMap U R X j hj.continuous).hom.c.app
      (op ((show IsOpenEmbedding
        (ringedSpaceMap U R X j hj.continuous).hom.base from hj).functor.obj V))) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  let baseEmbedding : IsOpenEmbedding
      (ringedSpaceMap U R X j hj.continuous).hom.base := hj
  let W : Opens X := baseEmbedding.functor.obj V
  let homeo : inverseImage U X j hj.continuous W ≃ₜ W :=
    hj.homeomorphOfSubsetRange (Set.image_subset_range j V.1)
  constructor
  · intro first second equal_pullbacks
    change (sheaf X R).presheaf.obj (op W) at first second
    apply TopCat.Hom.ext
    ext point
    have equal_values := congrArg
      (fun (pulled : (sheaf U R).presheaf.obj
          (op (inverseImage U X j hj.continuous W))) =>
        pulled (homeo.symm point))
      equal_pullbacks
    change first (homeo (homeo.symm point)) =
      second (homeo (homeo.symm point)) at equal_values
    calc
      first point = first (homeo (homeo.symm point)) :=
        congrArg (fun element : W => first element) (homeo.apply_symm_apply point).symm
      _ = second (homeo (homeo.symm point)) := equal_values
      _ = second point :=
        congrArg (fun element : W => second element) (homeo.apply_symm_apply point)
  · intro targetSection
    change (sheaf U R).presheaf.obj (op (inverseImage U X j hj.continuous W))
      at targetSection
    refine ⟨TopCat.ofHom ⟨fun point => targetSection (homeo.symm point),
      targetSection.hom.continuous.comp homeo.symm.continuous⟩, ?_⟩
    apply TopCat.Hom.ext
    ext point
    change targetSection (homeo.symm ⟨j point.1, point.2⟩) = targetSection point
    have image_eq : (⟨j point.1, point.2⟩ : W) = homeo point := Subtype.ext rfl
    calc
      targetSection (homeo.symm ⟨j point.1, point.2⟩) =
          targetSection (homeo.symm (homeo point)) :=
        congrArg (fun element : W => targetSection (homeo.symm element)) image_eq
      _ = targetSection point :=
        congrArg (fun element : inverseImage U X j hj.continuous W =>
          targetSection element) (homeo.symm_apply_apply point)

/-- Every open embedding induces an open immersion for the actual precomposition
ringed-space morphism over any topological commutative ring. -/
instance ringedSpaceMap_isOpenImmersion (j : U → X)
    (hj : IsOpenEmbedding j) :
    SheafedSpace.IsOpenImmersion (ringedSpaceMap U R X j hj.continuous) where
  base_open := hj
  c_iso := ringedSpaceMap_c_iso U X R j hj

variable (K : Type u) [Field K] [TopologicalSpace K]
  [IsTopologicalDivisionRing K] [T1Space K]

/-- On the image of each source open, the actual precomposition component of an open
embedding is an isomorphism, by the general ringed-space result. -/
theorem locallyRingedSpaceMap_c_iso (j : U → X) (hj : IsOpenEmbedding j)
    (V : Opens U) :
    IsIso ((locallyRingedSpaceMap U K X j hj.continuous).c.app
      (op ((show IsOpenEmbedding
        (locallyRingedSpaceMap U K X j hj.continuous).base from hj).functor.obj V))) := by
  change IsIso ((ringedSpaceMap U K X j hj.continuous).hom.c.app
    (op ((show IsOpenEmbedding
      (ringedSpaceMap U K X j hj.continuous).hom.base from hj).functor.obj V)))
  exact ringedSpaceMap_c_iso U X K j hj V

/-- Every open embedding induces an open immersion for the existing, actual
continuous-function locally ringed-space morphism. -/
instance locallyRingedSpaceMap_isOpenImmersion (j : U → X)
    (hj : IsOpenEmbedding j) :
    LocallyRingedSpace.IsOpenImmersion
      (locallyRingedSpaceMap U K X j hj.continuous) where
  base_open := hj
  c_iso := locallyRingedSpaceMap_c_iso U X K j hj

/-- The induced locally ringed space on an open subtype is isomorphic to the
intrinsic continuous-function locally ringed space of that subtype. -/
def restrictLocallyRingedSpaceIso (A : Opens X) :
    (locallyRingedSpace X K).restrict A.isOpenEmbedding ≅
      locallyRingedSpace A K := by
  letI : LocallyRingedSpace.IsOpenImmersion
      (locallyRingedSpaceMap A K X Subtype.val A.isOpenEmbedding'.continuous) :=
    locallyRingedSpaceMap_isOpenImmersion A X K Subtype.val A.isOpenEmbedding'
  exact (LocallyRingedSpace.IsOpenImmersion.isoRestrict
    (locallyRingedSpaceMap A K X Subtype.val A.isOpenEmbedding'.continuous)).symm

/-- The forward open-subtype comparison, followed by inclusion, is the
canonical restriction map into the ambient locally ringed space. -/
theorem restrictLocallyRingedSpaceIso_hom_ofRestrict (A : Opens X) :
    (restrictLocallyRingedSpaceIso X K A).hom ≫
        locallyRingedSpaceMap A K X Subtype.val A.isOpenEmbedding'.continuous =
      (locallyRingedSpace X K).ofRestrict A.isOpenEmbedding := by
  haveI : LocallyRingedSpace.IsOpenImmersion
      (locallyRingedSpaceMap A K X Subtype.val A.isOpenEmbedding'.continuous) :=
    locallyRingedSpaceMap_isOpenImmersion A X K Subtype.val A.isOpenEmbedding'
  exact LocallyRingedSpace.IsOpenImmersion.isoRestrict_inv_ofRestrict
    (locallyRingedSpaceMap A K X Subtype.val A.isOpenEmbedding'.continuous)

/-- The reverse open-subtype comparison, followed by the canonical restriction
map, is the actual precomposition morphism of the subtype inclusion. -/
theorem restrictLocallyRingedSpaceIso_inv_ofRestrict (A : Opens X) :
    (restrictLocallyRingedSpaceIso X K A).inv ≫
        (locallyRingedSpace X K).ofRestrict A.isOpenEmbedding =
      locallyRingedSpaceMap A K X Subtype.val A.isOpenEmbedding'.continuous := by
  haveI : LocallyRingedSpace.IsOpenImmersion
      (locallyRingedSpaceMap A K X Subtype.val A.isOpenEmbedding'.continuous) :=
    locallyRingedSpaceMap_isOpenImmersion A X K Subtype.val A.isOpenEmbedding'
  exact LocallyRingedSpace.IsOpenImmersion.isoRestrict_hom_ofRestrict
    (locallyRingedSpaceMap A K X Subtype.val A.isOpenEmbedding'.continuous)

end ContinuousFunctions
