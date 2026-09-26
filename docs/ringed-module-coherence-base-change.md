# Module pullback coherence and push–pull mates

Import `RingedSpaces` for the public aggregate, or import
`RingedSpaces.Modules.PullbackCoherence` and
`RingedSpaces.Modules.BaseChange` directly. The root-only client
[`Test/RingedSpaceBaseChange.lean`](../Test/RingedSpaceBaseChange.lean) exercises
both leaves and a non-Cartesian example. In these modules `X`, `Y`, `Z` and
`W` are commutative `RingedSpace.{u,u}` objects and every arrow is a **full**
ringed-space morphism, not merely a map of their underlying topological spaces.
Empty spaces and zero rings are permitted; no nonzero-ring or nonempty-space
instance is required.

## Actual module functors

`PullbackCoherence.ModuleSheaves X` is the category of sheaves of modules over
`RingedSpacePushforward.ringSheaf X`. For `f : X ⟶ Y`, `R f` is the full
structure-map module pushforward, `L f` is the explicit right-factor tensor
pullback from [`RingedSpacePullback`](ringed-space-pullback.md), and `A f` is
their **actual adjunction**. First the continuous module inverse image is
sheafified; then extension of scalars along the coefficient map is built from
the right-factor tensor presheaf and sheafified. Sections on an arbitrary open
are not identified with an un-sheafified tensor product. `A f` is an adjunction
between these actual functors, not an adjunction inferred from an unspecified
isomorphism of underlying base maps.

For `f : X ⟶ Y` and `g : Y ⟶ Z`, the direct-image comparison
`pushforwardComp f g : R f ⋙ R g ≅ R (f ≫ g)` uses the composite full
structure map and mathlib's module-sheaf pushforward composition.
`pushforwardId X : R (𝟙 X) ≅ 𝟭 (ModuleSheaves X)` handles identity.
The corresponding oriented inverse-image comparisons are

```lean
pullbackComp f g : L g ⋙ L f ≅ L (f ≫ g)
pullbackId X : L (𝟙 X) ≅ 𝟭 (ModuleSheaves X)
```

They arise by adjoint mates, **not** by equality of the functors. The
`pullbackComp_inverse_mate` and `pullbackId_mate` statements identify their
orientation relative to `pushforwardComp` and `pushforwardId`;
`pullbackComp_unit` identifies the comparison through the adjunction units.
Both `pushforwardComp_*Unit` and `pullbackComp_*Unit` give the oriented identity
laws; `pushforwardComp_assoc` and `pullbackComp_assoc` give associativity,
including the associator of functor composition. `pullbackComp_naturality`
states naturality on module morphisms. None asserts strict equality of
composite and single-arrow pullback functors.

## Square comparison

Given arrows `bottom : W ⟶ X`, `left : W ⟶ Y`, `top : X ⟶ Z`,
`right : Y ⟶ Z` and `commutes : bottom ≫ top = left ≫ right`,
`BaseChange.pushforwardSquare` is an iso between the two direct-image routes.
Taking its mate under the actual `A bottom` and `A right` yields

```lean
pushPull bottom left top right commutes :
  R top ⋙ L right ⟶ L bottom ⋙ R left
```

Each component sends a module sheaf over `X` from `(L right).obj
((R top).obj M)` to `(R left).obj ((L bottom).obj M)` over `Y`.
`pushPull_transpose` computes the adjunction transpose, while `pushPull_unit`
characterizes it by the two units and the full direct-image comparison;
`pushPull_unique` proves componentwise uniqueness from that identity.
`pushPull_naturality` handles module maps. `pushPull_section_smul` proves
linearity on every open and `pushPull_restrict` proves compatibility with open
restriction, both using the bundled morphism of module sheaves.

For the square with identity vertical arrows, `sourceIdentity top` and
`targetIdentity top` orient the pullback-identity isomorphisms on the two
sides of `pushPull`. `pushPull_identity_inverse` transports the inverse
comparison, and `pushPull_identity_normalized` shows that after applying the
target normalization the **actual mate** equals the source normalization.
This is an identity-square result, not a general `IsIso` result.

The client also constructs a point ringed space using the zero ring `ZMod 1`,
an empty inverse-image corner and the full map from that corner to the point.
`nonCartesianComparison` uses `pushPull` on the resulting commutative square;
`square_notCartesian` derives a contradiction from any claimed `IsPullback`
by obtaining a point of the empty carrier. The comparison therefore needs no
Cartesian square, flatness condition or claimed invertibility. Its proofs do
not imply an unqualified base-change isomorphism or a raw-section formula.

This direct import builds against mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5` and Lean
`leanprover/lean4:v4.34.0-rc2`. The historical 33-module
[`API.md`](API.md) snapshot predates these two leaves and is not their API
documentation. This guide describes the usable library API, regardless of its
release stage; destination acceptance, release and source-level coverage are
distinct decisions.
