/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/

/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import RingedSpaces.Restriction

/-!
# Gluing morphisms of ringed spaces along open covers

Compatible morphisms from the canonical restrictions of a ringed space to the members of
an indexed open cover glue to a unique morphism of ringed spaces. The restrictions and
equalities here are in the category of ringed spaces, including their structure-sheaf maps.

The construction uses the sheafed-space gluing machinery in mathlib. Its internal comparison
between the glued multicoequalizer and the original ringed space is proved by checking the
carrier topology, injectivity, stalk maps, and surjectivity. The proof of the categorical
transition maps is adapted from the generic portion of mathlib's
`Mathlib/AlgebraicGeometry/Gluing.lean` (Andrew Yang, Apache 2.0); no scheme hypotheses
are used here. The comparison proof is adapted from a previously reviewed research proof.

The present universe boundary is diagonal: the source, target and cover index live in
`RingedSpace.{u, u}` and `Type u`, respectively.

## References

* Mathlib, `Mathlib/AlgebraicGeometry/Gluing.lean` (Andrew Yang): the generic
  categorical transition-map construction adapted in the gluing proof.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology

namespace AlgebraicGeometry.RingedSpace

universe u

/-- A small indexed open cover of a ringed space. The family may be empty when the source
is empty, and any member of the family may itself be empty. -/
structure OpenCover (X : RingedSpace.{u, u}) where
  /-- The type indexing the members of the cover. -/
  J : Type u
  /-- The indexed open subsets of the underlying topological space. -/
  U : J → Opens X
  /-- Each point of the source belongs to some member. -/
  covers : ∀ x : X, ∃ i, x ∈ U i

namespace OpenCover

variable {X : RingedSpace.{u, u}} (C : OpenCover X)

/-- The canonical restriction of the ringed space to a cover member. -/
abbrev obj (i : C.J) : RingedSpace.{u, u} :=
  X.restrict (C.U i).isOpenEmbedding

/-- The canonical inclusion of a restricted member into the ringed space, as a full morphism. -/
abbrev ι (i : C.J) : C.obj i ⟶ X :=
  X.ofRestrict (C.U i).isOpenEmbedding

private noncomputable def transition (i j k : C.J) :
    pullback (pullback.fst (C.ι i) (C.ι j)) (pullback.fst (C.ι i) (C.ι k)) ⟶
      pullback (pullback.fst (C.ι j) (C.ι k)) (pullback.fst (C.ι j) (C.ι i)) := by
  refine (pullbackRightPullbackFstIso _ _ _).hom ≫ ?_
  refine ?_ ≫ (pullbackSymmetry _ _).hom
  refine ?_ ≫ (pullbackRightPullbackFstIso _ _ _).inv
  refine pullback.map _ _ _ _ (pullbackSymmetry _ _).hom (𝟙 _) (𝟙 _) ?_ ?_
  · simp [pullback.condition]
  · simp

set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc]
private theorem transition_fst_fst (i j k : C.J) :
    C.transition i j k ≫ pullback.fst _ _ ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ pullback.snd _ _ := by
  delta transition
  simp

set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc]
private theorem transition_fst_snd (i j k : C.J) :
    C.transition i j k ≫ pullback.fst _ _ ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ pullback.snd _ _ := by
  delta transition
  simp

set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc]
private theorem transition_snd_fst (i j k : C.J) :
    C.transition i j k ≫ pullback.snd _ _ ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ pullback.snd _ _ := by
  delta transition
  simp

set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc]
private theorem transition_snd_snd (i j k : C.J) :
    C.transition i j k ≫ pullback.snd _ _ ≫ pullback.snd _ _ =
      pullback.fst _ _ ≫ pullback.fst _ _ := by
  delta transition
  simp

private theorem transition_cocycle_fst (i j k : C.J) :
    C.transition i j k ≫ C.transition j k i ≫ C.transition k i j ≫ pullback.fst _ _ =
      pullback.fst _ _ := by
  apply pullback.hom_ext <;> simp

private theorem transition_cocycle_snd (i j k : C.J) :
    C.transition i j k ≫ C.transition j k i ≫ C.transition k i j ≫ pullback.snd _ _ =
      pullback.snd _ _ := by
  apply pullback.hom_ext <;> simp [pullback.condition]

private theorem transition_cocycle (i j k : C.J) :
    C.transition i j k ≫ C.transition j k i ≫ C.transition k i j = 𝟙 _ := by
  apply pullback.hom_ext <;> simp_rw [Category.id_comp, Category.assoc]
  · apply C.transition_cocycle_fst
  · apply C.transition_cocycle_snd

private noncomputable def glueData : SheafedSpace.GlueData CommRingCat where
  J := C.J
  U := C.obj
  V := fun ⟨i, j⟩ ↦ pullback (C.ι i) (C.ι j)
  f _ _ := pullback.fst _ _
  f_id _ := inferInstance
  t _ _ := (pullbackSymmetry _ _).hom
  t_id _ := by simp
  t' i j k := C.transition i j k
  t_fac i j k := by apply pullback.hom_ext <;> simp
  cocycle i j k := C.transition_cocycle i j k
  f_open _ _ := inferInstance

private noncomputable abbrev glued : RingedSpace.{u, u} :=
  C.glueData.toGlueData.glued

private noncomputable abbrev gluedι (i : C.J) : C.obj i ⟶ C.glued :=
  C.glueData.toGlueData.ι i

private theorem inclusion_compatibility (i j : C.J) :
    C.glueData.toGlueData.f i j ≫ C.ι i =
      (C.glueData.toGlueData.t i j ≫ C.glueData.toGlueData.f j i) ≫ C.ι j := by
  dsimp only [glueData]
  simpa only [pullbackSymmetry_hom_comp_fst] using
    (pullback.condition (f := C.ι i) (g := C.ι j))

private noncomputable def fromGlued : C.glued ⟶ X := by
  fapply Multicoequalizer.desc
  · exact C.ι
  rintro ⟨i, j⟩
  exact C.inclusion_compatibility i j

@[simp, reassoc]
private theorem gluedι_fromGlued (i : C.J) : C.gluedι i ≫ C.fromGlued = C.ι i :=
  Multicoequalizer.π_desc _ _ _ _ _

local notation "topGlueData" =>
  C.glueData.toPresheafedSpaceGlueData.toTopGlueData.toGlueData

set_option linter.style.haveILetI false in
private noncomputable def isoCarrier :
    C.glued.carrier ≅ (topGlueData).glued := by
  letI : ∀ i j k, PreservesLimit
      (cospan (C.glueData.toPresheafedSpaceGlueData.f i j)
        (C.glueData.toPresheafedSpaceGlueData.f i k))
      (PresheafedSpace.forget CommRingCat) := fun i j k ↦ by
    letI : PresheafedSpace.IsOpenImmersion
        (C.glueData.toPresheafedSpaceGlueData.f i j) :=
      C.glueData.toPresheafedSpaceGlueData.f_open i j
    exact PresheafedSpace.IsOpenImmersion.forget_preservesLimitsOfLeft _ _
  refine (PresheafedSpace.forget CommRingCat).mapIso C.glueData.isoPresheafedSpace ≪≫ ?_
  exact CategoryTheory.GlueData.gluedIso
    C.glueData.toPresheafedSpaceGlueData.toGlueData (PresheafedSpace.forget CommRingCat)

set_option backward.isDefEq.respectTransparency false in
@[simp]
private theorem topι_isoCarrier_inv (i : C.J) :
    (topGlueData).ι i ≫ C.isoCarrier.inv = (C.gluedι i).hom.base := by
  delta isoCarrier
  rw [Iso.trans_inv, CategoryTheory.GlueData.ι_gluedIso_inv_assoc, Functor.mapIso_inv,
    ← Functor.map_comp, C.glueData.ι_isoPresheafedSpace_inv i]
  rfl

private def Rel (a b : Σ i, C.obj i) : Prop :=
  ∃ z : C.glueData.V (a.1, b.1),
    (C.glueData.f _ _).hom.base z = a.2 ∧
      (C.glueData.t _ _ ≫ C.glueData.f _ _).hom.base z = b.2

set_option backward.isDefEq.respectTransparency.types false in
private theorem gluedι_eq_iff (i j : C.J) (x : C.obj i) (y : C.obj j) :
    (C.gluedι i).hom.base x = (C.gluedι j).hom.base y ↔
      C.Rel ⟨i, x⟩ ⟨j, y⟩ := by
  refine Iff.trans ?_ (TopCat.GlueData.ι_eq_iff_rel
    C.glueData.toPresheafedSpaceGlueData.toTopGlueData i j x y)
  rw [← ((TopCat.mono_iff_injective C.isoCarrier.inv).mp _).eq_iff,
    ← ConcreteCategory.comp_apply]
  · simp_rw [← C.topι_isoCarrier_inv]
    rfl
  · infer_instance

set_option backward.isDefEq.respectTransparency.types false in
private theorem isOpen_iff (S : Set C.glued.carrier) :
    IsOpen S ↔ ∀ i, IsOpen ((C.gluedι i).hom.base ⁻¹' S) := by
  rw [← (TopCat.homeoOfIso C.isoCarrier.symm).isOpen_preimage,
    TopCat.GlueData.isOpen_iff]
  apply forall_congr'
  intro i
  rw [← Set.preimage_comp, ← C.topι_isoCarrier_inv]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
private theorem fromGlued_injective : Function.Injective C.fromGlued.hom.base := by
  intro x y h
  obtain ⟨i, x, rfl⟩ := C.glueData.ι_jointly_surjective x
  obtain ⟨j, y, rfl⟩ := C.glueData.ι_jointly_surjective y
  change (C.gluedι i ≫ C.fromGlued).hom.base x =
    (C.gluedι j ≫ C.fromGlued).hom.base y at h
  rw [C.gluedι_fromGlued, C.gluedι_fromGlued] at h
  let comparison :=
    (TopCat.pullbackConeIsLimit _ _).conePointUniqueUpToIso
      (isLimitOfHasPullbackOfPreservesLimit (SheafedSpace.forget CommRingCat)
        (C.ι i) (C.ι j))
  change (C.gluedι i).hom.base x = (C.gluedι j).hom.base y
  rw [C.gluedι_eq_iff]
  use comparison.hom ⟨⟨x, y⟩, h⟩
  constructor
  · erw [← ConcreteCategory.comp_apply comparison.hom,
      IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingCospan.left]
    rfl
  · erw [← ConcreteCategory.comp_apply comparison.hom, pullbackSymmetry_hom_comp_fst,
      IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingCospan.right]
    rfl

set_option backward.isDefEq.respectTransparency false in
private theorem fromGlued_stalkMap_isIso (x : C.glued.carrier) :
    IsIso (C.fromGlued.hom.stalkMap x) := by
  obtain ⟨i, x, rfl⟩ := C.glueData.ι_jointly_surjective x
  have hcomp : (C.gluedι i).hom ≫ C.fromGlued.hom = (C.ι i).hom := by
    change (C.gluedι i ≫ C.fromGlued).hom = (C.ι i).hom
    exact congrArg
      (fun f : C.obj i ⟶ X ↦ InducedCategory.Hom.hom f) (C.gluedι_fromGlued i)
  have h := PresheafedSpace.stalkMap.congr_hom _ _ hcomp x
  rw [PresheafedSpace.stalkMap.comp, ← IsIso.eq_comp_inv] at h
  change IsIso (C.fromGlued.hom.stalkMap ((C.gluedι i).hom.base x))
  rw [h]
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem isOpenMap_fromGlued : IsOpenMap C.fromGlued.hom.base := by
  intro S hS
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  rw [C.isOpen_iff] at hS
  obtain ⟨i, hxi⟩ := C.covers x
  use C.fromGlued.hom.base '' S ∩ Set.range (C.ι i).hom.base
  use Set.inter_subset_left
  constructor
  · rw [← Set.image_preimage_eq_inter_range]
    apply (C.U i).isOpenEmbedding.isOpenMap
    convert! hS i using 1
    simp only [← C.gluedι_fromGlued i, SheafedSpace.comp_hom_base, TopCat.hom_comp,
      ContinuousMap.coe_comp, Set.preimage_comp]
    exact congrArg (fun T ↦ (C.gluedι i).hom.base ⁻¹' T)
      (Set.preimage_image_eq S C.fromGlued_injective)
  · exact ⟨hx, ⟨⟨x, hxi⟩, rfl⟩⟩

private theorem isOpenEmbedding_fromGlued : IsOpenEmbedding C.fromGlued.hom.base :=
  .of_continuous_injective_isOpenMap (by fun_prop) C.fromGlued_injective C.isOpenMap_fromGlued

private theorem fromGlued_base_epi : Epi C.fromGlued.hom.base := by
  rw [TopCat.epi_iff_surjective]
  intro x
  obtain ⟨i, hxi⟩ := C.covers x
  use (C.gluedι i).hom.base ⟨x, hxi⟩
  change (C.gluedι i ≫ C.fromGlued).hom.base ⟨x, hxi⟩ = x
  rw [C.gluedι_fromGlued]
  rfl

private theorem fromGlued_isIso : IsIso C.fromGlued := by
  have (x : C.glued.carrier) : IsIso (C.fromGlued.hom.stalkMap x) :=
    C.fromGlued_stalkMap_isIso x
  have : Epi C.fromGlued.hom.base := C.fromGlued_base_epi
  have : SheafedSpace.IsOpenImmersion C.fromGlued :=
    SheafedSpace.IsOpenImmersion.of_stalk_iso _ C.isOpenEmbedding_fromGlued
  exact SheafedSpace.IsOpenImmersion.to_iso C.fromGlued

private noncomputable def glueMorphismsOriginal {Y : RingedSpace.{u, u}}
    (f : ∀ i, C.obj i ⟶ Y)
    (hf : ∀ i j, pullback.fst (C.ι i) (C.ι j) ≫ f i =
      pullback.snd (C.ι i) (C.ι j) ≫ f j) : X ⟶ Y := by
  have : IsIso C.fromGlued := C.fromGlued_isIso
  refine inv C.fromGlued ≫ ?_
  fapply Multicoequalizer.desc
  · exact f
  rintro ⟨i, j⟩
  dsimp only [glueData]
  change pullback.fst _ _ ≫ f i = ((pullbackSymmetry _ _).hom ≫ pullback.fst _ _) ≫ f j
  simpa only [pullbackSymmetry_hom_comp_fst] using hf i j

/-- Glue pairwise compatible full morphisms from the canonical open restrictions to a target
ringed space. Compatibility is equality of morphisms from each categorical pullback. -/
noncomputable def glueMorphisms {Y : RingedSpace.{u, u}} (f : ∀ i, C.obj i ⟶ Y)
    (hf : ∀ i j, pullback.fst (C.ι i) (C.ι j) ≫ f i =
      pullback.snd (C.ι i) (C.ι j) ≫ f j) : X ⟶ Y := by
  let transition (i j k : C.J) :
      pullback (pullback.fst (C.ι i) (C.ι j)) (pullback.fst (C.ι i) (C.ι k)) ⟶
        pullback (pullback.fst (C.ι j) (C.ι k)) (pullback.fst (C.ι j) (C.ι i)) := by
    refine (pullbackRightPullbackFstIso _ _ _).hom ≫ ?_
    refine ?_ ≫ (pullbackSymmetry _ _).hom
    refine ?_ ≫ (pullbackRightPullbackFstIso _ _ _).inv
    refine pullback.map _ _ _ _ (pullbackSymmetry _ _).hom (𝟙 _) (𝟙 _) ?_ ?_
    · simp [pullback.condition]
    · simp
  set_option backward.isDefEq.respectTransparency false in
  have transition_fst_fst (i j k : C.J) :
      transition i j k ≫ pullback.fst _ _ ≫ pullback.fst _ _ =
        pullback.fst _ _ ≫ pullback.snd _ _ := by
    dsimp only [transition]
    simp
  set_option backward.isDefEq.respectTransparency false in
  have transition_fst_snd (i j k : C.J) :
      transition i j k ≫ pullback.fst _ _ ≫ pullback.snd _ _ =
        pullback.snd _ _ ≫ pullback.snd _ _ := by
    dsimp only [transition]
    simp
  set_option backward.isDefEq.respectTransparency false in
  have transition_snd_fst (i j k : C.J) :
      transition i j k ≫ pullback.snd _ _ ≫ pullback.fst _ _ =
        pullback.fst _ _ ≫ pullback.snd _ _ := by
    dsimp only [transition]
    simp
  set_option backward.isDefEq.respectTransparency false in
  have transition_snd_snd (i j k : C.J) :
      transition i j k ≫ pullback.snd _ _ ≫ pullback.snd _ _ =
        pullback.fst _ _ ≫ pullback.fst _ _ := by
    dsimp only [transition]
    simp
  have transition_cocycle_fst (i j k : C.J) :
      transition i j k ≫ transition j k i ≫ transition k i j ≫ pullback.fst _ _ =
        pullback.fst _ _ := by
    apply pullback.hom_ext <;> simp [transition_fst_fst, transition_fst_snd,
      transition_snd_snd]
  have transition_cocycle_snd (i j k : C.J) :
      transition i j k ≫ transition j k i ≫ transition k i j ≫ pullback.snd _ _ =
        pullback.snd _ _ := by
    apply pullback.hom_ext <;> simp [transition_fst_snd,
      transition_snd_fst, transition_snd_snd, pullback.condition]
  let data : SheafedSpace.GlueData CommRingCat :=
    { J := C.J
      U := C.obj
      V := fun ⟨i, j⟩ ↦ pullback (C.ι i) (C.ι j)
      f _ _ := pullback.fst _ _
      f_id _ := inferInstance
      t _ _ := (pullbackSymmetry _ _).hom
      t_id _ := by simp
      t' i j k := transition i j k
      t_fac i j k := by
        apply pullback.hom_ext
        · simp [transition_snd_fst]
        · simp [transition_snd_snd]
      cocycle i j k := by
        apply pullback.hom_ext <;> simp_rw [Category.id_comp, Category.assoc]
        · exact transition_cocycle_fst i j k
        · exact transition_cocycle_snd i j k
      f_open _ _ := inferInstance }
  have compatibility (i j : C.J) :
      data.toGlueData.f i j ≫ C.ι i =
        (data.toGlueData.t i j ≫ data.toGlueData.f j i) ≫ C.ι j := by
    dsimp only [data]
    simpa only [pullbackSymmetry_hom_comp_fst] using
      (pullback.condition (f := C.ι i) (g := C.ι j))
  let fromGlued : data.toGlueData.glued ⟶ X := by
    fapply Multicoequalizer.desc
    · exact C.ι
    rintro ⟨i, j⟩
    exact compatibility i j
  let gluedι (i : C.J) : C.obj i ⟶ data.toGlueData.glued :=
    data.toGlueData.ι i
  have gluedι_fromGlued (i : C.J) : gluedι i ≫ fromGlued = C.ι i :=
    Multicoequalizer.π_desc _ _ _ _ _
  have : IsIso fromGlued := by
    let topData := data.toPresheafedSpaceGlueData.toTopGlueData.toGlueData
    set_option linter.style.haveILetI false in
    let isoCarrier : data.toGlueData.glued.carrier ≅ topData.glued := by
      letI : ∀ i j k, PreservesLimit
          (cospan (data.toPresheafedSpaceGlueData.f i j)
            (data.toPresheafedSpaceGlueData.f i k))
          (PresheafedSpace.forget CommRingCat) := fun i j k ↦ by
        letI : PresheafedSpace.IsOpenImmersion
            (data.toPresheafedSpaceGlueData.f i j) :=
          data.toPresheafedSpaceGlueData.f_open i j
        exact PresheafedSpace.IsOpenImmersion.forget_preservesLimitsOfLeft _ _
      refine (PresheafedSpace.forget CommRingCat).mapIso data.isoPresheafedSpace ≪≫ ?_
      exact CategoryTheory.GlueData.gluedIso
        data.toPresheafedSpaceGlueData.toGlueData (PresheafedSpace.forget CommRingCat)
    have topι_isoCarrier_inv (i : C.J) :
        topData.ι i ≫ isoCarrier.inv = (gluedι i).hom.base := by
      dsimp only [isoCarrier]
      rw [Iso.trans_inv, CategoryTheory.GlueData.ι_gluedIso_inv_assoc, Functor.mapIso_inv,
        ← Functor.map_comp, data.ι_isoPresheafedSpace_inv i]
      rfl
    let rel (a b : Σ i, C.obj i) : Prop :=
      ∃ z : data.V (a.1, b.1),
        (data.f _ _).hom.base z = a.2 ∧
          (data.t _ _ ≫ data.f _ _).hom.base z = b.2
    set_option backward.isDefEq.respectTransparency.types false in
    have gluedι_eq_iff (i j : C.J) (x : C.obj i) (y : C.obj j) :
        (gluedι i).hom.base x = (gluedι j).hom.base y ↔
          rel ⟨i, x⟩ ⟨j, y⟩ := by
      refine Iff.trans ?_ (TopCat.GlueData.ι_eq_iff_rel
        data.toPresheafedSpaceGlueData.toTopGlueData i j x y)
      rw [← ((TopCat.mono_iff_injective isoCarrier.inv).mp _).eq_iff,
        ← ConcreteCategory.comp_apply]
      · simp_rw [← topι_isoCarrier_inv]
        rfl
      · infer_instance
    set_option backward.isDefEq.respectTransparency.types false in
    have isOpen_iff (S : Set data.toGlueData.glued.carrier) :
        IsOpen S ↔ ∀ i, IsOpen ((gluedι i).hom.base ⁻¹' S) := by
      rw [← (TopCat.homeoOfIso isoCarrier.symm).isOpen_preimage,
        TopCat.GlueData.isOpen_iff]
      apply forall_congr'
      intro i
      rw [← Set.preimage_comp, ← topι_isoCarrier_inv]
      rfl
    set_option backward.isDefEq.respectTransparency.types false in
    have fromGlued_injective : Function.Injective fromGlued.hom.base := by
      intro x y h
      obtain ⟨i, x, rfl⟩ := data.ι_jointly_surjective x
      obtain ⟨j, y, rfl⟩ := data.ι_jointly_surjective y
      change (gluedι i ≫ fromGlued).hom.base x =
        (gluedι j ≫ fromGlued).hom.base y at h
      rw [gluedι_fromGlued, gluedι_fromGlued] at h
      let comparison :=
        (TopCat.pullbackConeIsLimit _ _).conePointUniqueUpToIso
          (isLimitOfHasPullbackOfPreservesLimit (SheafedSpace.forget CommRingCat)
            (C.ι i) (C.ι j))
      change (gluedι i).hom.base x = (gluedι j).hom.base y
      rw [gluedι_eq_iff]
      use comparison.hom ⟨⟨x, y⟩, h⟩
      constructor
      · erw [← ConcreteCategory.comp_apply comparison.hom,
          IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingCospan.left]
        rfl
      · erw [← ConcreteCategory.comp_apply comparison.hom, pullbackSymmetry_hom_comp_fst,
          IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingCospan.right]
        rfl
    set_option backward.isDefEq.respectTransparency false in
    have fromGlued_stalkMap_isIso (x : data.toGlueData.glued.carrier) :
        IsIso (fromGlued.hom.stalkMap x) := by
      obtain ⟨i, x, rfl⟩ := data.ι_jointly_surjective x
      have hcomp : (gluedι i).hom ≫ fromGlued.hom = (C.ι i).hom := by
        change (gluedι i ≫ fromGlued).hom = (C.ι i).hom
        exact congrArg
          (fun morphism : C.obj i ⟶ X ↦ InducedCategory.Hom.hom morphism)
          (gluedι_fromGlued i)
      haveI : SheafedSpace.IsOpenImmersion (data.toGlueData.ι i) :=
        data.ιIsOpenImmersion i
      haveI : IsIso ((data.toGlueData.ι i).hom.stalkMap x) :=
        SheafedSpace.IsOpenImmersion.stalk_iso (data.toGlueData.ι i) x
      have h := PresheafedSpace.stalkMap.congr_hom _ _ hcomp x
      rw [PresheafedSpace.stalkMap.comp, ← IsIso.eq_comp_inv] at h
      change IsIso (fromGlued.hom.stalkMap ((gluedι i).hom.base x))
      rw [h]
      infer_instance
    set_option backward.isDefEq.respectTransparency.types false in
    set_option backward.defeqAttrib.useBackward true in
    have isOpenMap_fromGlued : IsOpenMap fromGlued.hom.base := by
      intro S hS
      rw [isOpen_iff_forall_mem_open]
      intro x hx
      rw [isOpen_iff] at hS
      obtain ⟨i, hxi⟩ := C.covers x
      use fromGlued.hom.base '' S ∩ Set.range (C.ι i).hom.base
      use Set.inter_subset_left
      constructor
      · rw [← Set.image_preimage_eq_inter_range]
        apply (C.U i).isOpenEmbedding.isOpenMap
        convert! hS i using 1
        simp only [← gluedι_fromGlued i, SheafedSpace.comp_hom_base, TopCat.hom_comp,
          ContinuousMap.coe_comp, Set.preimage_comp]
        exact congrArg (fun subset ↦ (gluedι i).hom.base ⁻¹' subset)
          (Set.preimage_image_eq S fromGlued_injective)
      · exact ⟨hx, ⟨⟨x, hxi⟩, rfl⟩⟩
    have isOpenEmbedding_fromGlued : IsOpenEmbedding fromGlued.hom.base :=
      .of_continuous_injective_isOpenMap (by fun_prop) fromGlued_injective isOpenMap_fromGlued
    have fromGlued_base_epi : Epi fromGlued.hom.base := by
      rw [TopCat.epi_iff_surjective]
      intro x
      obtain ⟨i, hxi⟩ := C.covers x
      use (gluedι i).hom.base ⟨x, hxi⟩
      change (gluedι i ≫ fromGlued).hom.base ⟨x, hxi⟩ = x
      rw [gluedι_fromGlued]
      rfl
    have (x : data.toGlueData.glued.carrier) : IsIso (fromGlued.hom.stalkMap x) :=
      fromGlued_stalkMap_isIso x
    have : Epi fromGlued.hom.base := fromGlued_base_epi
    have : SheafedSpace.IsOpenImmersion fromGlued :=
      SheafedSpace.IsOpenImmersion.of_stalk_iso _ isOpenEmbedding_fromGlued
    exact SheafedSpace.IsOpenImmersion.to_iso fromGlued
  refine inv fromGlued ≫ ?_
  fapply Multicoequalizer.desc
  · exact f
  rintro ⟨i, j⟩
  change pullback.fst _ _ ≫ f i = ((pullbackSymmetry _ _).hom ≫ pullback.fst _ _) ≫ f j
  simpa only [pullbackSymmetry_hom_comp_fst] using hf i j

private theorem glueMorphisms_eq_original {Y : RingedSpace.{u, u}}
    (f : ∀ i, C.obj i ⟶ Y)
    (hf : ∀ i j, pullback.fst (C.ι i) (C.ι j) ≫ f i =
      pullback.snd (C.ι i) (C.ι j) ≫ f j) :
    C.glueMorphisms f hf = C.glueMorphismsOriginal f hf := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The glued full morphism restricts literally to each prescribed cover-member morphism. -/
@[reassoc]
theorem ι_glueMorphisms {Y : RingedSpace.{u, u}} (f : ∀ i, C.obj i ⟶ Y)
    (hf : ∀ i j, pullback.fst (C.ι i) (C.ι j) ≫ f i =
      pullback.snd (C.ι i) (C.ι j) ≫ f j) (i : C.J) :
    C.ι i ≫ C.glueMorphisms f hf = f i := by
  rw [C.glueMorphisms_eq_original]
  have : IsIso C.fromGlued := C.fromGlued_isIso
  rw [← C.gluedι_fromGlued i]
  simp only [Category.assoc, glueMorphismsOriginal, IsIso.hom_inv_id_assoc]
  apply Multicoequalizer.π_desc

set_option backward.isDefEq.respectTransparency false in
/-- Full morphisms from a ringed space are equal if their restrictions to every cover member
are equal, including the induced maps of structure sheaves. -/
theorem hom_ext {Y : RingedSpace.{u, u}} (f g : X ⟶ Y)
    (h : ∀ i, C.ι i ≫ f = C.ι i ≫ g) : f = g := by
  let comparison : C.glued ⟶ X := C.fromGlued
  have heq : comparison ≫ f = comparison ≫ g := by
    apply Multicoequalizer.hom_ext
    intro i
    dsimp only [comparison]
    change (C.gluedι i ≫ C.fromGlued) ≫ f = (C.gluedι i ≫ C.fromGlued) ≫ g
    rw [C.gluedι_fromGlued, h]
  have : IsIso C.fromGlued := C.fromGlued_isIso
  exact (cancel_epi comparison).mp heq

/-- A compatible family of full morphisms on an arbitrary indexed open cover has exactly
one extension to the original ringed space. The transition-map step adapts Andrew Yang's
Mathlib gluing construction; the full ringed-space comparison is proved here. -/
theorem existsUnique_gluing {Y : RingedSpace.{u, u}} (f : ∀ i, C.obj i ⟶ Y)
    (hf : ∀ i j, pullback.fst (C.ι i) (C.ι j) ≫ f i =
      pullback.snd (C.ι i) (C.ι j) ≫ f j) :
    ∃! g : X ⟶ Y, ∀ i, C.ι i ≫ g = f i := by
  refine ⟨C.glueMorphisms f hf, ?_, ?_⟩
  · intro i
    exact C.ι_glueMorphisms f hf i
  intro g' hg
  apply C.hom_ext
  intro i
  rw [hg i, C.ι_glueMorphisms]

/-- Full-morphism compatibility on the literal pairwise open restrictions is equivalent
to compatibility on categorical pullbacks. No choice of pullback model is required
by a caller using the literal-intersection condition. -/
theorem pullback_compatibility_iff_intersection {Y : RingedSpace.{u, u}}
    (f : ∀ i, C.obj i ⟶ Y) :
    (∀ i j, pullback.fst (C.ι i) (C.ι j) ≫ f i =
      pullback.snd (C.ι i) (C.ι j) ≫ f j) ↔
    (∀ i j, restrictMap (C.U i ⊓ C.U j) (C.U i) inf_le_left ≫ f i =
      restrictMap (C.U i ⊓ C.U j) (C.U j) inf_le_right ≫ f j) := by
  constructor
  · intro hf i j
    let h := isPullback_restrictInf (C.U i) (C.U j)
    have heq := congrArg
      (fun t : pullback (C.ι i) (C.ι j) ⟶ Y => h.isoPullback.hom ≫ t) (hf i j)
    simpa only [← Category.assoc, h.isoPullback_hom_fst,
      h.isoPullback_hom_snd] using heq
  · intro hf i j
    let h := isPullback_restrictInf (C.U i) (C.U j)
    apply (cancel_epi h.isoPullback.hom).mp
    simpa only [← Category.assoc, h.isoPullback_hom_fst,
      h.isoPullback_hom_snd] using hf i j

/-- A family of full morphisms agreeing on literal pairwise intersections extends
uniquely to the entire ringed space. In particular, this covers empty intersections,
empty cover members, infinite covers and the empty cover of an empty space. -/
theorem existsUnique_gluing_of_intersection {Y : RingedSpace.{u, u}}
    (f : ∀ i, C.obj i ⟶ Y)
    (hf : ∀ i j, restrictMap (C.U i ⊓ C.U j) (C.U i) inf_le_left ≫ f i =
      restrictMap (C.U i ⊓ C.U j) (C.U j) inf_le_right ≫ f j) :
    ∃! g : X ⟶ Y, ∀ i, C.ι i ≫ g = f i :=
  C.existsUnique_gluing f ((C.pullback_compatibility_iff_intersection f).mpr hf)

end OpenCover
end AlgebraicGeometry.RingedSpace

#lint-
