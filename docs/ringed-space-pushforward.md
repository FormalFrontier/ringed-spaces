# Pushforward through a full morphism of ringed spaces

Vakil's *The Rising Sea: Foundations of Algebraic Geometry* (21 October 2025
draft), Definition 7.2.1 (p. 204) and Exercise 7.2.D(c,e) (p. 205), request
pushforward along a **full** ringed-space morphism and its adjunction with
pullback. The entire structure map supplies the coefficients here; comparison
with Mathlib's inverse-image and pushforward functors is a project proof.

Import `RingedSpaces.Modules.RingedSpacePushforward` directly or the public
`RingedSpaces` aggregate. The root-only full-morphism client
[`RingedSpacesTests/RingedSpaceFullMorphismRoot.lean`](../RingedSpacesTests/RingedSpaceFullMorphismRoot.lean)
checks the public export; `RingedSpacesTests.RingedSpacePushforwardRootCoexist` checks
root-plus-direct compatibility, not an independent root-only import.

Let `X` and `Y` be ringed spaces in diagonal universe `u` and let `f : X ⟶ Y`
be **any full ringed-space morphism**. Write `g = f.hom.base`,
`A = (TopCat.Sheaf.pullback CommRingCat g).obj Y.sheaf`, and let
`R_X` and `R_Y` be their commutative structure sheaves considered as sheaves
of ordinary rings. The functor `SheafInverseImage.sheafForget` is the established
sheaf-compatible `CommRingCat`-to-`RingCat` transport; no alternative module
category, restriction functor, or coefficient action is introduced here.

## Coefficient maps

The existing `SheafInverseImage.actualUnit g Y.sheaf` is the commutative-ring
inverse-image/pushforward **unit forgotten to ring sheaves**:

```text
η : R_Y ⟶ g_* (forget A).
```

`ringSheafMap f` forgets the adjoint `RingedSpace.inverseImageMap f : A ⟶ X.sheaf`
of the *entire original structure map* `f.hom.c`. The public `structureMap f`
forgets the actual sheaf morphism corresponding to `f.hom.c`:

```text
θ : forget A ⟶ R_X,
σ : R_Y ⟶ g_* R_X.
```

`structureMap_original f U r` identifies its value with `f.hom.c.app U r`
at every target open `U` and coefficient section `r`. The theorem
`actualUnit_comp_ringSheafMap f` establishes **the full morphism equality**

```text
η ≫ (TopCat.Sheaf.pushforward RingCat g).map θ = σ.
```

It is obtained by applying the existing commutativity-forgetting sheaf functor
to `RingedSpace.inverseImageMap_unit f`, using the previously established
`SheafInverseImage.pushforwardForget_map` and functoriality. In particular,
`structureMap_apply f U r` gives the action on every target open; this is not
just equality of base continuous functions or of underlying additive maps.

## Module comparison

The public `pushforwardFunctor f` is the native
`SheafOfModules.pushforward (structureMap f)` from modules over `R_X` to
modules over `R_Y`. The natural isomorphism `restrictPushforwardIso f` has type

```text
SheafOfModules.restrictScalars θ ⋙
  SheafInverseImage.pushforwardFunctor g Y.sheaf ≅ pushforwardFunctor f.
```

It composes mathlib's `SheafOfModules.pushforwardComp` for the identity site
functor on `Opens X` with `SheafOfModules.pushforwardCongr` for the proven
equality of complete coefficient maps. Both components are identity maps on
each underlying section (`restrictPushforwardIso_hom_app` and
`restrictPushforwardIso_inv_app`); `restrictPushforwardIso_smul` and
`restrictPushforwardIso_inv_smul` prove linearity for the actual `R_Y` action,
which by definition of the native pushforward uses `σ`.
`restrictPushforwardIso_inverseLaws` and `restrictPushforwardIso_naturality`
give the two laws and naturality in module-sheaf morphisms, with an additional
pointwise equation `restrictPushforwardIso_naturality_apply`. The comparison
does not construct a tensor pullback,
identify a chosen pullback, or establish a ringed-space composition law.

The theorems require no nonempty spaces, nonzero rings, stalk-locality, or
schemes. `RingedSpacesTests.RingedSpacePushforwardConcrete` uses a verified proper open of
the discrete two-point space, a nonidentity collapse map, the actual canonical
full ringed-space map with its sectionwise equations, an empty source space,
and the zero ring `ZMod 1`. Its other coefficient example uses `ZMod 5`;
the clients do not assert nonzero sections of the resulting sheafification.

## Dependencies and attribution

The implementation imports `RingedSpaces.InverseImage` and
`RingedSpaces.Modules.SheafInverseImageHom`, and mathlib at
`83abb3e776bdefcbc447a1e44d0debe4010039e5`, Lean `v4.34.0-rc2`.
`SheafInverseImage.sheafForget` and `pushforwardForget_map` are reused as-is.
The underlying `SheafOfModules.pushforwardComp`, `pushforwardCongr`, and
`restrictScalars` are from mathlib files
`Mathlib/Algebra/Category/ModuleCat/Sheaf/PushforwardContinuous.lean` and
`Mathlib/Algebra/Category/ModuleCat/Sheaf/ChangeOfRings.lean` by Joël Riou.
This leaf does not import a source-specific research repository and makes no
source-coverage claim.
