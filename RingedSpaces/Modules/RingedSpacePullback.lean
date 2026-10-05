/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import RingedSpaces.Modules.RingedSpacePushforward
public import RingedSpaces.Modules.SheafChangeOfRingsSymmetry
public import Mathlib.CategoryTheory.Adjunction.Unique

set_option warningAsError true

/-!
# Explicit pullback of module sheaves through a ringed-space morphism

First take the genuine sheafified inverse image of modules, then sheafify the
right-factor tensor presheaf along the full inverse-image map of structure
sheaves. Its right adjoint is pushforward along the original full morphism.
No assertion identifies arbitrary sections of a sheafification with raw tensors.

## References

* Ravi Vakil, *The Rising Sea: Foundations of Algebraic Geometry* (21 October 2025
  draft), Definition 7.2.1 (p. 204) and Exercise 7.2.D(b,c,e) (p. 205):
  full-morphism pullback and its pushforward adjunction motivate the functors.
  §2.6.4 and Exercise 2.6.K(a) (p. 92) motivate the tensor presheaf followed
  by sheafification; §2.7.2 (p. 93) the temporary inverse-image presheaf.
  The right-tensor order, bundled Hom adjunction and natural isomorphism with
  Mathlib's chosen pullback are further project/Mathlib constructions.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

namespace RingedSpaces.Modules.RingedSpacePullback

universe u

variable {X Y : AlgebraicGeometry.RingedSpace.{u, u}} (f : X ⟶ Y)

/-- The commutative-ring sheaf pulled back along the underlying continuous map. -/
noncomputable abbrev inverseRing : X.carrier.Sheaf CommRingCat.{u} :=
  (TopCat.Sheaf.pullback CommRingCat.{u} f.hom.base).obj Y.sheaf

/-- Coefficient map supplied by the entire ringed-space morphism. -/
noncomputable abbrev coefficientMap : inverseRing f ⟶ X.sheaf :=
  AlgebraicGeometry.RingedSpace.inverseImageMap f

/-- The explicit right-tensor, sheafified pullback.
Vakil's *The Rising Sea* (21 October 2025 draft), Exercise 7.2.D(b)
(p. 205), requests full-morphism pullback; the project construction
sheafifies a genuine right-factor tensor after inverse image. -/
noncomputable def pullbackFunctor :
    SheafOfModules.{u} (RingedSpacePushforward.ringSheaf Y) ⥤
      SheafOfModules.{u} (RingedSpacePushforward.ringSheaf X) := by
  letI := opensWeakSheafify X.carrier
  letI := opensWEqualsLocallyBijective X.carrier
  exact SheafInverseImage.moduleFunctor f.hom.base Y.sheaf ⋙
    rightSheafFunctor (inverseRing f) X.sheaf (coefficientMap f)

/-- Tensor symmetry on the already sheafified inverse-image module. -/
noncomputable def tensorComparison :
    pullbackFunctor f ≅
      SheafInverseImage.moduleFunctor f.hom.base Y.sheaf ⋙
        tensorSheafFunctor (inverseRing f) X.sheaf (coefficientMap f) := by
  letI := opensWeakSheafify X.carrier
  letI := opensWEqualsLocallyBijective X.carrier
  exact (Functor.isoWhiskerLeft
    (SheafInverseImage.moduleFunctor f.hom.base Y.sheaf)
    (opensRightSheafNatIso (inverseRing f) X.sheaf (coefficientMap f)))

/-- Forgotten full inverse-image coefficients agree with tensor restriction coefficients. -/
theorem coefficientMap_ringSheafMap :
    ringSheafMap (inverseRing f) X.sheaf (coefficientMap f) =
      RingedSpacePushforward.ringSheafMap f := by
  rfl

/-- Right-tensor sheaf extension is left adjoint to full-morphism pushforward.
Vakil's *The Rising Sea* (21 October 2025 draft), Exercise 7.2.D(e)
(p. 205), requests this adjunction; the bundled proof uses Mathlib and
the complete structure map rather than raw tensor sections. -/
noncomputable def adjunction :
    pullbackFunctor f ⊣ RingedSpacePushforward.pushforwardFunctor f := by
  letI := opensWeakSheafify X.carrier
  letI := opensWEqualsLocallyBijective X.carrier
  let composed := (SheafInverseImage.adjunction f.hom.base Y.sheaf).comp
    (tensorSheafAdjunction (inverseRing f) X.sheaf (coefficientMap f))
  have baseAdj : pullbackFunctor f ⊣
      SheafOfModules.restrictScalars (RingedSpacePushforward.ringSheafMap f) ⋙
        SheafInverseImage.pushforwardFunctor f.hom.base Y.sheaf := by
    exact composed.ofNatIsoLeft (tensorComparison f).symm
  exact baseAdj.ofNatIsoRight (RingedSpacePushforward.restrictPushforwardIso f)

/-- The bundled Hom equivalence, natural in both module variables.
This is the project's formal Hom-adjunction realization of Vakil's
*The Rising Sea* (21 October 2025 draft), Exercise 7.2.D(e) (p. 205). -/
noncomputable def homEquiv
    (M : SheafOfModules.{u} (RingedSpacePushforward.ringSheaf Y))
    (N : SheafOfModules.{u} (RingedSpacePushforward.ringSheaf X)) :
    ((pullbackFunctor f).obj M ⟶ N) ≃
      (M ⟶ (RingedSpacePushforward.pushforwardFunctor f).obj N) :=
  (adjunction f).homEquiv M N

/-- Forward transpose in terms of inverse image, tensor extension and full pushforward. -/
theorem homEquiv_apply
    (M : SheafOfModules.{u} (RingedSpacePushforward.ringSheaf Y))
    (N : SheafOfModules.{u} (RingedSpacePushforward.ringSheaf X))
    (h : (pullbackFunctor f).obj M ⟶ N) :
    homEquiv f M N h =
      (SheafInverseImage.adjunction f.hom.base Y.sheaf).homEquiv M _
        ((tensorSheafAdjunction (inverseRing f) X.sheaf (coefficientMap f)).homEquiv _ N
          ((tensorComparison f).inv.app M ≫ h)) ≫
        (RingedSpacePushforward.restrictPushforwardIso f).hom.app N := by
  rfl

/-- The forward and backward transposes are mutually inverse. -/
theorem homEquiv_inverse_laws
    (M : SheafOfModules.{u} (RingedSpacePushforward.ringSheaf Y))
    (N : SheafOfModules.{u} (RingedSpacePushforward.ringSheaf X)) :
    (∀ h, (homEquiv f M N).symm (homEquiv f M N h) = h) ∧
      (∀ k, homEquiv f M N ((homEquiv f M N).symm k) = k) :=
  ⟨(homEquiv f M N).left_inv, (homEquiv f M N).right_inv⟩

/-- Naturality in the source module. -/
theorem homEquiv_naturality_left
    {M M' : SheafOfModules.{u} (RingedSpacePushforward.ringSheaf Y)}
    (g : M' ⟶ M) (N : SheafOfModules.{u} (RingedSpacePushforward.ringSheaf X))
    (h : (pullbackFunctor f).obj M ⟶ N) :
    homEquiv f M' N ((pullbackFunctor f).map g ≫ h) =
      g ≫ homEquiv f M N h :=
  (adjunction f).homEquiv_naturality_left g h

/-- Naturality in the target module. -/
theorem homEquiv_naturality_right
    (M : SheafOfModules.{u} (RingedSpacePushforward.ringSheaf Y))
    {N N' : SheafOfModules.{u} (RingedSpacePushforward.ringSheaf X)}
    (h : (pullbackFunctor f).obj M ⟶ N) (g : N ⟶ N') :
    homEquiv f M N' (h ≫ g) =
      homEquiv f M N h ≫ (RingedSpacePushforward.pushforwardFunctor f).map g :=
  (adjunction f).homEquiv_naturality_right h g

/-- The full unit: inverse-image unit, then tensor unit transported by symmetry,
then the component of the full pushforward comparison. -/
theorem unit_formula
    (M : SheafOfModules.{u} (RingedSpacePushforward.ringSheaf Y)) :
    (adjunction f).unit.app M =
      (SheafInverseImage.adjunction f.hom.base Y.sheaf).unit.app M ≫
        (SheafInverseImage.pushforwardFunctor f.hom.base Y.sheaf).map
          ((tensorSheafAdjunction (inverseRing f) X.sheaf (coefficientMap f)).unit.app
            ((SheafInverseImage.moduleFunctor f.hom.base Y.sheaf).obj M) ≫
            (SheafOfModules.restrictScalars
              (RingedSpacePushforward.ringSheafMap f)).map
                ((tensorComparison f).inv.app M)) ≫
        (RingedSpacePushforward.restrictPushforwardIso f).hom.app
          ((pullbackFunctor f).obj M) := by
  rfl

/-- The two triangle identities of the full adjunction. -/
theorem triangle_identities
    (M : SheafOfModules.{u} (RingedSpacePushforward.ringSheaf Y))
    (N : SheafOfModules.{u} (RingedSpacePushforward.ringSheaf X)) :
    (pullbackFunctor f).map ((adjunction f).unit.app M) ≫
        (adjunction f).counit.app ((pullbackFunctor f).obj M) = 𝟙 _ ∧
      (adjunction f).unit.app ((RingedSpacePushforward.pushforwardFunctor f).obj N) ≫
        (RingedSpacePushforward.pushforwardFunctor f).map ((adjunction f).counit.app N) =
          𝟙 _ :=
  ⟨(adjunction f).left_triangle_components M, (adjunction f).right_triangle_components N⟩

/-- The native pullback's right-adjoint instance comes from this explicit construction. -/
noncomputable instance fullPushforwardIsRightAdjoint :
    (SheafOfModules.pushforward (RingedSpacePushforward.structureMap f)).IsRightAdjoint :=
  (adjunction f).isRightAdjoint

/-- The native pullback's right-adjoint instance comes from this explicit construction. -/
noncomputable def nativeAdjunction :
    SheafOfModules.pullback (RingedSpacePushforward.structureMap f) ⊣
      RingedSpacePushforward.pushforwardFunctor f :=
  SheafOfModules.pullbackPushforwardAdjunction _

/-- Compare explicit right-tensor pullback with the pinned native pullback. -/
noncomputable def nativeComparison :
    pullbackFunctor f ≅ SheafOfModules.pullback (RingedSpacePushforward.structureMap f) :=
  (adjunction f).leftAdjointUniq (nativeAdjunction f)

/-- The native comparison carries the explicit unit to the native unit. -/
theorem nativeComparison_unit
    (M : SheafOfModules.{u} (RingedSpacePushforward.ringSheaf Y)) :
    (adjunction f).unit.app M ≫
      (RingedSpacePushforward.pushforwardFunctor f).map
        ((nativeComparison f).hom.app M) = (nativeAdjunction f).unit.app M :=
  Adjunction.unit_leftAdjointUniq_hom_app (adjunction f) (nativeAdjunction f) M

/-- The comparison also carries the native counit back to the explicit counit. -/
theorem nativeComparison_counit
    (N : SheafOfModules.{u} (RingedSpacePushforward.ringSheaf X)) :
    (nativeComparison f).hom.app ((RingedSpacePushforward.pushforwardFunctor f).obj N) ≫
      (nativeAdjunction f).counit.app N = (adjunction f).counit.app N :=
  Adjunction.leftAdjointUniq_hom_app_counit (adjunction f) (nativeAdjunction f) N

/-- The native comparison intertwines both transposes, not merely the functors. -/
theorem nativeComparison_homEquiv
    (M : SheafOfModules.{u} (RingedSpacePushforward.ringSheaf Y))
    (N : SheafOfModules.{u} (RingedSpacePushforward.ringSheaf X))
    (h : (SheafOfModules.pullback (RingedSpacePushforward.structureMap f)).obj M ⟶ N) :
    homEquiv f M N ((nativeComparison f).hom.app M ≫ h) =
      (nativeAdjunction f).homEquiv M N h := by
  rw [homEquiv, (adjunction f).homEquiv_naturality_right, nativeComparison,
    Adjunction.homEquiv_leftAdjointUniq_hom_app]
  exact ((nativeAdjunction f).homEquiv_unit M N h).symm

end RingedSpaces.Modules.RingedSpacePullback

#lint
