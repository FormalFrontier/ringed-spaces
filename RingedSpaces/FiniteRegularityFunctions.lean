/-
Copyright (c) 2023 Heather Macbeth. All rights reserved.
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Adam Topaz, Formal Frontier Agents
-/
module

public import Mathlib.Geometry.Manifold.Sheaf.LocallyRingedSpace
public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import RingedSpaces.ContinuousFunctions

/-!
# Finite-regularity scalar function sheaves

For a charted space with model `IM` over a nontrivially normed field `𝕜`, the
sections on an open `U` are the bundled maps `C^(r : ℕ∞ω)⟮IM, U; 𝓘(𝕜), 𝕜⟯`.
Restriction is `ContMDiffMap.restrictRingHom`. The stalk evaluation is surjective,
and a germ is a unit precisely when its value is nonzero.

The sheaf construction requires no `IsManifold` instance. Such an instance is
needed when interpreting this chart-dependent regularity intrinsically on a
manifold with compatible changes of charts.

Smooth scalar sections restrict to finite-regularity sections. In order zero,
the sheaf is naturally isomorphic to the existing sheaf of continuous scalar
functions. These comparisons preserve restrictions and evaluation of germs.

The sheaf and evaluation adapt the construction in mathlib's
`Mathlib/Geometry/Manifold/Sheaf/Smooth.lean`, and the local-ring argument adapts
`Mathlib/Geometry/Manifold/Sheaf/LocallyRingedSpace.lean`, both at mathlib commit
`83abb3e776bdefcbc447a1e44d0debe4010039e5` (Apache-2.0).
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology Opposite
open scoped ContDiff Manifold

universe u

namespace FiniteRegularityFunctions

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  {HM : Type*} [TopologicalSpace HM] (IM : ModelWithCorners 𝕜 EM HM)
  (M : Type u) [TopologicalSpace M] [ChartedSpace HM M]

/-- The sheaf of types of bundled finite-`C^r` scalar functions. -/
def typeSheaf (r : ℕ) : TopCat.Sheaf (Type u) ↧M :=
  (contDiffWithinAt_localInvariantProp (I := IM) (I' := 𝓘(𝕜)) (r : ℕ∞ω)).sheaf M 𝕜

instance typeSheafCoeFun (r : ℕ) (U : (Opens (TopCat.of M))ᵒᵖ) :
    CoeFun ((typeSheaf IM M r).presheaf.obj U)
      (fun _ ↦ ↑(unop U) → 𝕜) where
  coe f := f.1

/-- The underlying type sheaf has bundled finite-regularity sections. -/
theorem typeSheaf_obj_eq (r : ℕ) (U : (Opens (TopCat.of M))ᵒᵖ) :
    (typeSheaf IM M r).presheaf.obj U =
      C^(r : ℕ∞ω)⟮IM, (unop U : Opens M); 𝓘(𝕜), 𝕜⟯ := by
  rfl

/-- Every type-sheaf section satisfies the finite-regularity predicate. -/
theorem typeSheaf_section_contMDiff (r : ℕ) (U : Opens M)
    (f : (typeSheaf IM M r).presheaf.obj (op U)) :
    ContMDiff IM 𝓘(𝕜) (r : ℕ∞ω) (fun point : U ↦ f point) := by
  exact f.2

instance (r : ℕ) (U : (Opens (TopCat.of M))ᵒᵖ) :
    CommRing ((typeSheaf IM M r).presheaf.obj U) :=
  inferInstanceAs <| CommRing C^(r : ℕ∞ω)⟮IM, (unop U : Opens M); 𝓘(𝕜), 𝕜⟯

/-- Restriction of bundled finite-`C^r` functions as a commutative-ring homomorphism. -/
def presheaf (r : ℕ) : TopCat.Presheaf CommRingCat.{u} ↧M :=
  { obj := fun U ↦ ↧((typeSheaf IM M r).presheaf.obj U)
    map := fun h ↦ CommRingCat.ofHom <|
      ContMDiffMap.restrictRingHom IM 𝓘(𝕜) 𝕜 <| CategoryTheory.leOfHom h.unop
    map_id := fun _ ↦ rfl
    map_comp := fun _ _ ↦ rfl }

/-- The commutative-ring sheaf of bundled finite-`C^r` scalar functions. -/
@[implicit_reducible]
def sheaf (r : ℕ) : TopCat.Sheaf CommRingCat.{u} ↧M where
  obj := presheaf IM M r
  property := by
    rw [CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget _ _
      (CategoryTheory.forget CommRingCat)]
    exact (typeSheaf IM M r).property

instance (r : ℕ) (U : (Opens (TopCat.of M))ᵒᵖ) :
    CoeFun ((sheaf IM M r).presheaf.obj U) (fun _ ↦ ↑(unop U) → 𝕜) where
  coe f := f.1

section Sections

variable {IM M}

/-- A ring-sheaf section is a bundled finite-regularity scalar map on its open set. -/
def sectionRingEquiv (r : ℕ) (U : Opens M) :
    (sheaf IM M r).presheaf.obj (op U) ≃+*
      C^(r : ℕ∞ω)⟮IM, U; 𝓘(𝕜), 𝕜⟯ := by
  exact RingEquiv.refl _

/-- Bundling a finite-regularity scalar function as a section. -/
def ofFunction (r : ℕ) (U : Opens M) (f : U → 𝕜)
    (hf : ContMDiff IM 𝓘(𝕜) (r : ℕ∞ω) f) :
    (sheaf IM M r).presheaf.obj (op U) := by
  exact ⟨f, hf⟩

/-- The underlying value of a bundled section is the original function. -/
@[simp] theorem ofFunction_apply (r : ℕ) (U : Opens M) (f : U → 𝕜)
    (hf : ContMDiff IM 𝓘(𝕜) (r : ℕ∞ω) f) (point : U) :
    ofFunction (IM := IM) (M := M) r U f hf point = f point := by
  rfl

/-- The bundled map corresponding to a section has the section's values. -/
@[simp] theorem sectionRingEquiv_apply (r : ℕ) (U : Opens M)
    (f : (sheaf IM M r).presheaf.obj (op U)) (point : U) :
    sectionRingEquiv (IM := IM) (M := M) r U f point = f point := by
  rfl

/-- Every finite-regularity section satisfies its characteristic predicate. -/
theorem section_contMDiff (r : ℕ) (U : Opens M)
    (f : (sheaf IM M r).presheaf.obj (op U)) :
    ContMDiff IM 𝓘(𝕜) (r : ℕ∞ω) (fun point : U ↦ f point) := by
  exact f.2

/-- Sections are determined by their scalar values on the open set. -/
@[ext] theorem section_ext (r : ℕ) (U : Opens M)
    {f g : (sheaf IM M r).presheaf.obj (op U)}
    (h : ∀ point : U, f point = g point) : f = g := by
  apply Subtype.ext
  exact funext h

/-- Forgetting the ring structure recovers the finite-regularity type sheaf. -/
theorem typeSheaf_forget (r : ℕ) :
    (CategoryTheory.sheafCompose _ (CategoryTheory.forget CommRingCat.{u})).obj
      (sheaf IM M r) = typeSheaf IM M r := by
  rfl

/-- The ring homomorphism restricting finite-regularity sections along an open inclusion. -/
def restrict (r : ℕ) {U V : Opens M} (h : U ≤ V) :
    (sheaf IM M r).presheaf.obj (op V) →+*
      (sheaf IM M r).presheaf.obj (op U) :=
  ((sheaf IM M r).presheaf.map h.hom.op).hom

/-- Restriction evaluates a section at the same point of the larger open. -/
@[simp] theorem restrict_apply (r : ℕ) {U V : Opens M} (h : U ≤ V)
    (f : (sheaf IM M r).presheaf.obj (op V)) (point : U) :
    restrict (IM := IM) (M := M) r h f point = f ⟨point.1, h point.2⟩ := by
  rfl

end Sections

/-- Evaluation at a point from sections on an open neighborhood. -/
def evalAt (r : ℕ) (x : TopCat.of M) (U : OpenNhds x) :
    (sheaf IM M r).presheaf.obj (op U.1) ⟶ ↧𝕜 :=
  CommRingCat.ofHom (ContMDiffMap.evalRingHom ⟨x, U.2⟩)

/-- Evaluation of a germ, as a morphism of commutative rings. -/
def evalHom (r : ℕ) (x : TopCat.of M) :
    (sheaf IM M r).presheaf.stalk x ⟶ ↧𝕜 := by
  refine colimit.desc _ ⟨_, ⟨fun U ↦ ?_, ?_⟩⟩
  · apply evalAt IM M r x
  · cat_disch

/-- Evaluation of a finite-`C^r` scalar germ at its base point. -/
def eval (r : ℕ) (x : M) : (sheaf IM M r).presheaf.stalk x →+* 𝕜 :=
  (evalHom IM M r x).hom

variable {IM M}

set_option backward.isDefEq.respectTransparency.types false in
@[simp, reassoc, elementwise] theorem ι_evalHom (r : ℕ) (x : TopCat.of M) (U) :
    colimit.ι ((OpenNhds.inclusion x).op ⋙ _) U ≫ evalHom IM M r x =
      evalAt IM M r x _ :=
  colimit.ι_desc _ _

/-- Evaluating the germ of a section returns its value at the point. -/
@[simp] theorem eval_germ (r : ℕ) (U : Opens M) (x : M) (hx : x ∈ U)
    (f : (sheaf IM M r).presheaf.obj (op U)) :
    eval IM M r x ((sheaf IM M r).presheaf.germ U x hx f) = f ⟨x, hx⟩ :=
  congrArg (fun hom ↦ hom f) <| ι_evalHom (IM := IM) (M := M) r x ⟨U, hx⟩

/-- Categorical stalk evaluation sends a germ to its representative's value. -/
@[simp] theorem evalHom_germ (r : ℕ) (U : Opens M) (x : M) (hx : x ∈ U)
    (f : (sheaf IM M r).presheaf.obj (op U)) :
    evalHom IM M r x ((sheaf IM M r).presheaf.germ U x hx f) = f ⟨x, hx⟩ := by
  exact eval_germ (IM := IM) (M := M) r U x hx f

/-- Every scalar value is represented by the germ of a constant section. -/
theorem eval_surjective (r : ℕ) (x : M) : Function.Surjective (eval IM M r x) := by
  intro scalar
  refine ⟨(sheaf IM M r).presheaf.germ ⊤ x (by simp)
    ⟨fun _ ↦ scalar, contMDiff_const⟩, ?_⟩
  simpa using (eval_germ (IM := IM) (M := M) r ⊤ x (by simp)
    (⟨fun _ ↦ scalar, contMDiff_const⟩ :
      (sheaf IM M r).presheaf.obj (op ⊤)))

instance (r : ℕ) (x : M) : Nontrivial ((sheaf IM M r).presheaf.stalk x) :=
  (eval_surjective (IM := IM) (M := M) r x).nontrivial

set_option backward.isDefEq.respectTransparency.types false in
/-- A scalar germ is invertible exactly when its value at the base point is nonzero. -/
theorem isUnit_stalk_iff (r : ℕ) {x : M}
    (germ : (sheaf IM M r).presheaf.stalk x) :
    IsUnit germ ↔ eval IM M r x germ ≠ 0 := by
  constructor
  · rintro ⟨⟨f, inverse, left_inverse, right_inverse⟩, rfl⟩ hzero
    simpa [hzero] using congrArg (eval IM M r x) left_inverse
  · let sections := (sheaf IM M r).presheaf
    intro hnonzero
    obtain ⟨U : Opens M, hxU, f : C^(r : ℕ∞ω)⟮IM, U; 𝓘(𝕜), 𝕜⟯, rfl⟩ :=
      sections.exists_germ_eq germ
    have hx_nonzero : f ⟨x, hxU⟩ ≠ 0 := by
      convert! hnonzero
      exact (eval_germ (IM := IM) (M := M) r U x hxU f).symm
    have eventually_nonzero : ∀ᶠ (point : U) in 𝓝 ⟨x, hxU⟩, f point ≠ 0 :=
      f.contMDiff.continuous.continuousAt.eventually_ne hx_nonzero
    rw [eventually_nhds_iff] at eventually_nonzero
    obtain ⟨V₀, hV₀_nonzero, hV₀_open, hxV₀⟩ := eventually_nonzero
    let V : Opens M := ⟨Subtype.val '' V₀, U.2.isOpenMap_subtype_val V₀ hV₀_open⟩
    have hVU : V ≤ U := Subtype.coe_image_subset (U : Set M) V₀
    have hV₀ : V₀ = Set.range (Set.inclusion hVU) := by
      convert! (Set.range_inclusion hVU).symm
      ext point
      change _ ↔ point ∈ Subtype.val ⁻¹' Subtype.val '' V₀
      rw [Set.preimage_image_eq _ Subtype.coe_injective]
    clear_value V
    subst hV₀
    have hxV : x ∈ (V : Set M) := by
      obtain ⟨point, hpoint⟩ := hxV₀
      convert! point.2
      exact congrArg Subtype.val hpoint.symm
    have restricted_nonzero : ∀ point : V, f (Set.inclusion hVU point) ≠ 0 :=
      fun point ↦ hV₀_nonzero (Set.inclusion hVU point) (Set.mem_range_self point)
    let inverse : C^(r : ℕ∞ω)⟮IM, V; 𝓘(𝕜), 𝕜⟯ :=
      ⟨(f ∘ Set.inclusion hVU)⁻¹,
        (f.contMDiff.comp (contMDiff_inclusion hVU)).inv₀ restricted_nonzero⟩
    refine ⟨⟨sections.germ _ x hxV
      (restrict (IM := IM) (M := M) r hVU f),
      sections.germ _ x hxV inverse, ?_, ?_⟩,
      sections.germ_res_apply hVU.hom x hxV f⟩
    · rw [← map_mul]
      convert! RingHom.map_one _
      apply Subtype.ext
      ext point
      exact mul_inv_cancel₀ (restricted_nonzero point)
    · rw [← map_mul]
      convert! RingHom.map_one _
      apply Subtype.ext
      ext point
      exact inv_mul_cancel₀ (restricted_nonzero point)

/-- The nonunits in a stalk are precisely the kernel of evaluation. -/
theorem nonunits_stalk (r : ℕ) (x : M) :
    nonunits ((sheaf IM M r).presheaf.stalk x) = RingHom.ker (eval IM M r x) := by
  ext germ
  rw [mem_nonunits_iff]
  change (¬ IsUnit germ) ↔ (eval IM M r x germ = 0)
  simpa only [not_ne_iff] using
    (isUnit_stalk_iff (IM := IM) (M := M) r germ).not

/-- The stalk of the finite-`C^r` scalar sheaf is a local ring. -/
instance instLocalRingStalk (r : ℕ) (x : M) :
    IsLocalRing ((sheaf IM M r).presheaf.stalk x) := by
  apply IsLocalRing.of_nonunits_add
  rw [nonunits_stalk (IM := IM) (M := M) r x]
  intro first second
  exact Ideal.add_mem _

/-- The locally ringed space associated with finite-`C^r` scalar functions. -/
@[implicit_reducible]
def locallyRingedSpace (r : ℕ) (IM : ModelWithCorners 𝕜 EM HM)
    (M : Type u) [TopologicalSpace M] [ChartedSpace HM M] : LocallyRingedSpace where
  carrier := ↧M
  presheaf := presheaf IM M r
  IsSheaf := (sheaf IM M r).property
  isLocalRing x := instLocalRingStalk (IM := IM) (M := M) r x

section Comparisons

/-- Restrict a smooth scalar section to finite order using `ContMDiff.of_le`. -/
def smoothToFiniteSection (r : ℕ) (U : Opens M) :
    (smoothSheafCommRing IM 𝓘(𝕜) M 𝕜).presheaf.obj (op U) →+*
      (sheaf IM M r).presheaf.obj (op U) where
  toFun representative :=
    ⟨representative, (show ContMDiff IM 𝓘(𝕜) ∞ (representative : U → 𝕜)
      from representative.2).of_le (by simp)⟩
  map_one' := by apply Subtype.ext; rfl
  map_mul' := by intros; apply Subtype.ext; rfl
  map_zero' := by apply Subtype.ext; rfl
  map_add' := by intros; apply Subtype.ext; rfl

/-- Weakening regularity does not change the scalar value of a smooth section. -/
@[simp] theorem smoothToFiniteSection_apply (r : ℕ) (U : Opens M)
    (f : (smoothSheafCommRing IM 𝓘(𝕜) M 𝕜).presheaf.obj (op U))
    (point : U) :
    smoothToFiniteSection (IM := IM) (M := M) r U f point = f point := by
  rfl

/-- The morphism from Mathlib's smooth scalar sheaf to the finite-`C^r` sheaf. -/
def smoothToFinite (r : ℕ) :
    smoothSheafCommRing IM 𝓘(𝕜) M 𝕜 ⟶ sheaf IM M r where
  hom.app U := CommRingCat.ofHom (smoothToFiniteSection (IM := IM) (M := M) r U.unop)
  hom.naturality := by
    intro U V inclusion
    ext representative
    rfl

/-- The smooth comparison is the order-weakening map on every open set. -/
theorem smoothToFinite_app (r : ℕ) (U : Opens M) :
    (smoothToFinite (IM := IM) (M := M) r).hom.app (op U) =
      CommRingCat.ofHom (smoothToFiniteSection (IM := IM) (M := M) r U) := by
  rfl

/-- Order weakening commutes with restriction to a smaller open. -/
theorem smoothToFinite_restrict (r : ℕ) {U V : Opens M} (h : U ≤ V)
    (f : (smoothSheafCommRing IM 𝓘(𝕜) M 𝕜).presheaf.obj (op V)) :
    restrict (IM := IM) (M := M) r h
        (smoothToFiniteSection (IM := IM) (M := M) r V f) =
      smoothToFiniteSection (IM := IM) (M := M) r U
        ((smoothSheafCommRing IM 𝓘(𝕜) M 𝕜).presheaf.map h.hom.op f) := by
  apply section_ext (IM := IM) (M := M) r U
  intro point
  rfl

/-- The induced map from smooth germs to finite-regularity germs. -/
def smoothToFiniteStalk (r : ℕ) (x : M) :
    (smoothSheafCommRing IM 𝓘(𝕜) M 𝕜).presheaf.stalk x ⟶
      (sheaf IM M r).presheaf.stalk x :=
  by
    simpa only [TopCat.Presheaf.stalkFunctor_obj] using
      (TopCat.Presheaf.stalkFunctor CommRingCat.{u} (x : TopCat.of M)).map
        (smoothToFinite (IM := IM) (M := M) r).hom

set_option backward.isDefEq.respectTransparency false in
/-- Weakening a represented smooth germ gives the germ of its weakened section. -/
@[simp] theorem smoothToFiniteStalk_germ (r : ℕ) (U : Opens M) (x : M)
    (hx : x ∈ U) (f : (smoothSheafCommRing IM 𝓘(𝕜) M 𝕜).presheaf.obj (op U)) :
    smoothToFiniteStalk (IM := IM) (M := M) r x
        ((smoothSheafCommRing IM 𝓘(𝕜) M 𝕜).presheaf.germ U x hx f) =
      (sheaf IM M r).presheaf.germ U x hx
        (smoothToFiniteSection (IM := IM) (M := M) r U f) := by
  have h := TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx
    (smoothToFinite (IM := IM) (M := M) r).hom f
  have happ : ((smoothToFinite (IM := IM) (M := M) r).hom.app (op U)) f =
      smoothToFiniteSection (IM := IM) (M := M) r U f := by
    rw [smoothToFinite_app]
    rfl
  rw [happ] at h
  simpa only [TopCat.Sheaf.presheaf, smoothToFiniteStalk,
    TopCat.Presheaf.stalkFunctor_obj] using h

/-- Smooth and finite stalk evaluation agree under order weakening. -/
theorem smoothToFiniteStalk_evalHom (r : ℕ) (x : M) :
    smoothToFiniteStalk (IM := IM) (M := M) r x ≫ evalHom IM M r x =
      smoothSheafCommRing.evalHom IM 𝓘(𝕜) M 𝕜 (x : TopCat.of M) := by
  apply TopCat.Presheaf.stalk_hom_ext
  intro U hxU
  ext representative
  change evalHom IM M r x
    (smoothToFiniteStalk (IM := IM) (M := M) r x
      ((smoothSheafCommRing IM 𝓘(𝕜) M 𝕜).presheaf.germ U x hxU representative)) =
    smoothSheafCommRing.evalHom IM 𝓘(𝕜) M 𝕜 x
      ((smoothSheafCommRing IM 𝓘(𝕜) M 𝕜).presheaf.germ U x hxU representative)
  rw [smoothToFiniteStalk_germ, evalHom_germ,
    smoothSheafCommRing.evalHom_germ, smoothToFiniteSection_apply]

/-- The comparison preserves and reflects units of smooth germs. -/
theorem smoothToFiniteStalk_isUnit_iff (r : ℕ) (x : M)
    (germ : (smoothSheafCommRing IM 𝓘(𝕜) M 𝕜).presheaf.stalk x) :
    IsUnit (smoothToFiniteStalk (IM := IM) (M := M) r x germ) ↔ IsUnit germ := by
  have heval : eval IM M r x (smoothToFiniteStalk (IM := IM) (M := M) r x germ) =
      smoothSheafCommRing.eval IM 𝓘(𝕜) M 𝕜 x germ := by
    simpa only [eval, smoothSheafCommRing.eval, CommRingCat.hom_comp,
      RingHom.coe_comp, Function.comp_apply] using congrArg (fun arrow ↦ arrow germ)
      (smoothToFiniteStalk_evalHom (IM := IM) (M := M) r x)
  rw [isUnit_stalk_iff (IM := IM) (M := M) r,
    smoothSheafCommRing.isUnit_stalk_iff]
  change eval IM M r x (smoothToFiniteStalk (IM := IM) (M := M) r x germ) ≠ 0 ↔
    smoothSheafCommRing.eval IM 𝓘(𝕜) M 𝕜 x germ ≠ 0
  rw [heval]

/-- The smooth-to-finite stalk comparison is a local ring homomorphism. -/
theorem smoothToFiniteStalk_isLocalHom (r : ℕ) (x : M) :
    IsLocalHom (smoothToFiniteStalk (IM := IM) (M := M) r x).hom := by
  exact ⟨fun germ h ↦ (smoothToFiniteStalk_isUnit_iff (IM := IM) (M := M) r x germ).mp h⟩

/-- Turn a zero-order scalar section into a section of the continuous-function sheaf. -/
def zeroToContinuous (U : Opens M) :
    (sheaf IM M 0).presheaf.obj (op U) →+*
      (ContinuousFunctions.sheaf M 𝕜).presheaf.obj (op U) where
  toFun representative := TopCat.ofHom
    ⟨representative, contMDiff_zero_iff.mp representative.2⟩
  map_one' := rfl
  map_mul' := fun _ _ ↦ rfl
  map_zero' := rfl
  map_add' := fun _ _ ↦ rfl

/-- At order zero, continuity of a scalar function gives a finite-order section. -/
def continuousToZero (U : Opens M) :
    (ContinuousFunctions.sheaf M 𝕜).presheaf.obj (op U) →+*
      (sheaf IM M 0).presheaf.obj (op U) where
  toFun representative :=
    ⟨representative, contMDiff_zero_iff.mpr representative.hom.continuous⟩
  map_one' := by apply Subtype.ext; rfl
  map_mul' := by intros; apply Subtype.ext; rfl
  map_zero' := by apply Subtype.ext; rfl
  map_add' := by intros; apply Subtype.ext; rfl

/-- The zero-order-to-continuous conversion preserves pointwise values. -/
@[simp] theorem zeroToContinuous_apply (U : Opens M)
    (f : (sheaf IM M 0).presheaf.obj (op U)) (point : U) :
    zeroToContinuous (IM := IM) (M := M) U f point = f point := by
  rfl

/-- The continuous-to-zero-order conversion preserves pointwise values. -/
@[simp] theorem continuousToZero_apply (U : Opens M)
    (f : (ContinuousFunctions.sheaf M 𝕜).presheaf.obj (op U)) (point : U) :
    continuousToZero (IM := IM) (M := M) U f point = f point := by
  rfl

/-- The two directions of the zero-order section conversion are inverse. -/
@[simp] theorem zeroToContinuous_continuousToZero (U : Opens M)
    (f : (ContinuousFunctions.sheaf M 𝕜).presheaf.obj (op U)) :
    zeroToContinuous (IM := IM) (M := M) U
      (continuousToZero (IM := IM) (M := M) U f) = f := by
  apply TopCat.ext
  intro point
  rfl

/-- The two directions of the zero-order section conversion are inverse. -/
@[simp] theorem continuousToZero_zeroToContinuous (U : Opens M)
    (f : (sheaf IM M 0).presheaf.obj (op U)) :
    continuousToZero (IM := IM) (M := M) U
      (zeroToContinuous (IM := IM) (M := M) U f) = f := by
  apply Subtype.ext
  rfl

/-- The zero-order scalar sheaf is naturally isomorphic to the existing continuous sheaf. -/
def zeroSheafIso :
    sheaf IM M 0 ≅ ContinuousFunctions.sheaf M 𝕜 := by
  let forward : sheaf IM M 0 ⟶ ContinuousFunctions.sheaf M 𝕜 :=
    { hom.app U := CommRingCat.ofHom (zeroToContinuous (IM := IM) (M := M) U.unop)
      hom.naturality := by
        intro U V inclusion
        ext representative
        rfl }
  let backward : ContinuousFunctions.sheaf M 𝕜 ⟶ sheaf IM M 0 :=
    { hom.app U := CommRingCat.ofHom (continuousToZero (IM := IM) (M := M) U.unop)
      hom.naturality := by
        intro U V inclusion
        ext representative
        rfl }
  refine ⟨forward, backward, ?_, ?_⟩
  · apply CategoryTheory.Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply ConcreteCategory.hom_ext
    intro representative
    exact continuousToZero_zeroToContinuous (IM := IM) (M := M) U.unop representative
  · apply CategoryTheory.Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply ConcreteCategory.hom_ext
    intro representative
    exact zeroToContinuous_continuousToZero (IM := IM) (M := M) U.unop representative

/-- The forward component of the zero-order sheaf isomorphism is section conversion. -/
theorem zeroSheafIso_hom_app (U : Opens M) :
    (zeroSheafIso (IM := IM) (M := M)).hom.hom.app (op U) =
      CommRingCat.ofHom (zeroToContinuous (IM := IM) (M := M) U) := by
  rfl

/-- The inverse component of the zero-order sheaf isomorphism is section conversion. -/
theorem zeroSheafIso_inv_app (U : Opens M) :
    (zeroSheafIso (IM := IM) (M := M)).inv.hom.app (op U) =
      CommRingCat.ofHom (continuousToZero (IM := IM) (M := M) U) := by
  rfl

/-- The zero-order section conversion commutes with restriction. -/
theorem zeroToContinuous_restrict {U V : Opens M} (h : U ≤ V)
    (f : (sheaf IM M 0).presheaf.obj (op V)) :
    (ContinuousFunctions.sheaf M 𝕜).presheaf.map h.hom.op
        (zeroToContinuous (IM := IM) (M := M) V f) =
      zeroToContinuous (IM := IM) (M := M) U
        (restrict (IM := IM) (M := M) 0 h f) := by
  apply TopCat.ext
  intro point
  rfl

/-- The inverse zero-order conversion also commutes with restriction. -/
theorem continuousToZero_restrict {U V : Opens M} (h : U ≤ V)
    (f : (ContinuousFunctions.sheaf M 𝕜).presheaf.obj (op V)) :
    restrict (IM := IM) (M := M) 0 h
        (continuousToZero (IM := IM) (M := M) V f) =
      continuousToZero (IM := IM) (M := M) U
        ((ContinuousFunctions.sheaf M 𝕜).presheaf.map h.hom.op f) := by
  apply section_ext (IM := IM) (M := M) 0 U
  intro point
  rfl

/-- The zero-order isomorphism induces a map to continuous-function germs. -/
def zeroToContinuousStalk (x : M) :
    (sheaf IM M 0).presheaf.stalk x ⟶
      (ContinuousFunctions.sheaf M 𝕜).presheaf.stalk x :=
  by
    simpa only [TopCat.Presheaf.stalkFunctor_obj] using
      (TopCat.Presheaf.stalkFunctor CommRingCat.{u} (x : TopCat.of M)).map
        (zeroSheafIso (IM := IM) (M := M)).hom.hom

set_option backward.isDefEq.respectTransparency false in
/-- The zero-order comparison takes a germ to the converted representative's germ. -/
@[simp] theorem zeroToContinuousStalk_germ (U : Opens M) (x : M) (hx : x ∈ U)
    (f : (sheaf IM M 0).presheaf.obj (op U)) :
    zeroToContinuousStalk (IM := IM) (M := M) x
        ((sheaf IM M 0).presheaf.germ U x hx f) =
      (ContinuousFunctions.sheaf M 𝕜).presheaf.germ U x hx
        (zeroToContinuous (IM := IM) (M := M) U f) := by
  have h := TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx
    (zeroSheafIso (IM := IM) (M := M)).hom.hom f
  have happ : ((zeroSheafIso (IM := IM) (M := M)).hom.hom.app (op U)) f =
      zeroToContinuous (IM := IM) (M := M) U f := by
    rw [zeroSheafIso_hom_app]
    rfl
  rw [happ] at h
  simpa only [TopCat.Sheaf.presheaf, zeroToContinuousStalk,
    TopCat.Presheaf.stalkFunctor_obj] using h

/-- Zero-order germ evaluation agrees with continuous-function germ evaluation. -/
theorem zeroToContinuousStalk_evalHom (x : M) :
    zeroToContinuousStalk (IM := IM) (M := M) x ≫
        ContinuousFunctions.evalHom M 𝕜 x = evalHom IM M 0 x := by
  apply TopCat.Presheaf.stalk_hom_ext
  intro U hxU
  ext representative
  change ContinuousFunctions.evalHom M 𝕜 x
    (zeroToContinuousStalk (IM := IM) (M := M) x
      ((sheaf IM M 0).presheaf.germ U x hxU representative)) =
    evalHom IM M 0 x ((sheaf IM M 0).presheaf.germ U x hxU representative)
  rw [zeroToContinuousStalk_germ, ContinuousFunctions.evalHom_germ,
    evalHom_germ, zeroToContinuous_apply]

/-- The zero-order stalk comparison preserves and reflects units. -/
theorem zeroToContinuousStalk_isUnit_iff (x : M)
    (germ : (sheaf IM M 0).presheaf.stalk x) :
    IsUnit (zeroToContinuousStalk (IM := IM) (M := M) x germ) ↔ IsUnit germ := by
  have heval : ContinuousFunctions.eval M 𝕜 x
      (zeroToContinuousStalk (IM := IM) (M := M) x germ) = eval IM M 0 x germ := by
    simpa only [ContinuousFunctions.eval, eval, CommRingCat.hom_comp,
      RingHom.coe_comp, Function.comp_apply] using congrArg (fun arrow ↦ arrow germ)
      (zeroToContinuousStalk_evalHom (IM := IM) (M := M) x)
  rw [ContinuousFunctions.isUnit_stalk_iff M 𝕜 x,
    isUnit_stalk_iff (IM := IM) (M := M) 0]
  change ContinuousFunctions.eval M 𝕜 x (zeroToContinuousStalk (IM := IM) (M := M) x germ)
    ≠ 0 ↔ eval IM M 0 x germ ≠ 0
  rw [heval]

/-- The zero-order stalk comparison is a local ring homomorphism. -/
theorem zeroToContinuousStalk_isLocalHom (x : M) :
    IsLocalHom (zeroToContinuousStalk (IM := IM) (M := M) x).hom := by
  exact ⟨fun germ h ↦ (zeroToContinuousStalk_isUnit_iff (IM := IM) (M := M) x germ).mp h⟩

end Comparisons

end FiniteRegularityFunctions
