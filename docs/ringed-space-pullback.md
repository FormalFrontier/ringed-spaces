# Explicit module pullback through a full ringed-space morphism

Import `RingedSpaces.Modules.RingedSpacePullback` directly or the public
`RingedSpaces` aggregate. The root-only full-morphism client
[`Test/RingedSpaceFullMorphismRoot.lean`](../Test/RingedSpaceFullMorphismRoot.lean)
checks the public export; `Test.RingedSpacePullbackRootCoexist` checks
root-plus-direct compatibility, not an independent root-only import.

For any morphism `f : X ⟶ Y` of commutative ringed spaces in diagonal universe
`u`, let `g = f.hom.base`, `A = (TopCat.Sheaf.pullback CommRingCat g).obj
Y.sheaf`, and `θ = RingedSpace.inverseImageMap f : A ⟶ X.sheaf`. The structure
sheaves are regarded as sheaves of ordinary rings using the established
`SheafInverseImage.sheafForget` functor. This construction requires neither
local homomorphisms nor nonempty spaces or nonzero rings.

## Construction and coefficient identification

`RingedSpacePullback.pullbackFunctor f` composes the actual sheafified module
inverse image `SheafInverseImage.moduleFunctor g Y.sheaf` with
`rightSheafFunctor A X.sheaf θ`. The latter first forms the **right-factor**
tensor presheaf and then sheafifies it. `coefficientMap_ringSheafMap` checks
that scalar restriction along `θ`, after forgetting commutativity, uses exactly
`RingedSpacePushforward.ringSheafMap f`. The two coefficient maps agree as
sheaf morphisms, not just as base maps. `tensorComparison` applies the
accepted `opensRightSheafNatIso` to the module already pulled back along `g`;
its inverse is used to transport the scalar-extension adjunction to the
explicit right-tensor functor.

The sheafification in both steps is genuine. In particular, **sections on
arbitrary opens are not asserted to be raw tensor products**. A pointwise
generator formula would need the corresponding two sheafification-unit maps,
and none is assumed or claimed here.

## Full adjunction and transposes

The composition of `SheafInverseImage.adjunction g Y.sheaf` with
`tensorSheafAdjunction A X.sheaf θ`, transported by `tensorComparison.symm`,
has right adjoint scalar restriction along `θ` followed by the continuous
module pushforward. `RingedSpacePushforward.restrictPushforwardIso f` identifies
that composite with `RingedSpacePushforward.pushforwardFunctor f`, whose
coefficient map is the forgotten *full* structure map `f.hom.c`. Thus
`RingedSpacePullback.adjunction f` is an adjunction of actual functors:

```text
right-tensor-pullback(f) ⊣ pushforward(full f).
```

`homEquiv f M N` is the bundled Hom equivalence. For a map `h : L_f M ⟶ N`,
`homEquiv_apply` states precisely that its forward transpose is: precompose
`h` with `tensorComparison.inv.app M`, transpose under tensor extension,
transpose again under inverse image, and finally postcompose with
`restrictPushforwardIso.hom.app N`. `homEquiv_inverse_laws` proves both
inverse laws and the two `homEquiv_naturality_*` statements prove naturality
in each module variable.

`unit_formula` expresses the unit as the inverse-image unit, followed by the
pushforward of the scalar-extension unit and of the inverse tensor comparison,
and then the component of the full pushforward isomorphism. The counit and
both triangle identities are available directly from `adjunction`; the
`triangle_identities` theorem packages the latter for downstream clients.

## Native pullback comparison

`fullPushforwardIsRightAdjoint` **derives** the native right-adjoint instance
from the explicit adjunction. Only after this instance is constructed do we
form `nativeAdjunction` using mathlib's
`SheafOfModules.pullbackPushforwardAdjunction` on
`RingedSpacePushforward.structureMap f`. `nativeComparison` is the canonical
left-adjoint uniqueness isomorphism between explicit and native pullbacks.
`nativeComparison_unit`, `nativeComparison_counit` and
`nativeComparison_homEquiv` verify that the comparison carries the units,
counits and **every Hom transpose** to the native ones. These equalities
establish an adjunction-level semantic bridge rather than merely an abstract
isomorphism of functors.

The code imports accepted fixed-space scalar extension, actual inverse image,
and full pushforward leaves, plus mathlib at
`83abb3e776bdefcbc447a1e44d0debe4010039e5` with Lean `v4.34.0-rc2`.
It duplicates none of the native identity, composition or coherence results.
The explicit base test works for arbitrary full `f`; the concrete tests reuse
the discrete two-point proper open and nonidentity full morphism, empty-source
and zero-ring boundary fixtures. The latter tests check formal typing and
identities, not nonvanishing sheafified tensor sections. This guide makes no
source-text, integration, coverage or release claim. The leaf received bounded
preparation acceptance before the September 26, 2026 combined
root/default-target assembly. Its review, integration, release and source-coverage
decisions are separate from that earlier preparation acceptance.
