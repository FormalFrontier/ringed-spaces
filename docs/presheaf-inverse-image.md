# Inverse-image module presheaves

Import `RingedSpaces.Modules.PresheafInverseImage` for the focused library or
`RingedSpaces` for its aggregate import. Names below live in
`RingedSpaces.Modules.PresheafInverseImage`. Neither a source repository nor
source-specific interpretation is a dependency.

## Mathematical construction

Fix `X Y : TopCat.{v}`, any continuous `f : X ⟶ Y`, a presheaf
`R : Y.Presheaf RingCat.{v}` of possibly noncommutative unital rings, and
`M : PresheafOfModules.{v} R`. Put `L := (Opens.map f).op`. The coefficient
ring on `X` is **exactly** `L.pointwiseLeftKanExtension R`, not a chosen
abstract left adjoint or a ring transported from a separately chosen pullback.
The underlying additive presheaf of `inverseImageModule f R M` is definitionally
`L.pointwiseLeftKanExtension M.presheaf`. No sheaf condition, open-map, point,
nonzero-ring, finite, flatness or locality assumption is needed. The two
topological universes and the ring/module universe are the same `v`;
this does not assert a mixed-universe construction.

For an open `U ⊆ X`, `index f U` is the category of neighborhoods of `f(U)`:
an object consists of an open `V ⊆ Y` with `U ⊆ f⁻¹(V)`. Its arrows follow
restriction to smaller neighborhoods. The intersection of two such `V`'s
gives a common successor. In particular, this category is filtered and
nonempty even for the empty space or empty open. The values of the Kan
extensions on `U` are the colimit of ring and additive sections over this
same category. The construction reuses mathlib's
`PresheafOfModules.ModuleColimit` for the varying-ring module action, its
`smul_eq` on simultaneous generators and its `jointly_surjective₂` for
arbitrary ring/module elements. It does not reimplement generic filtered
colimits. Double-opposite transport and the colimit isomorphisms are private.

Writing `ιᴿᵢ` and `ιᴹᵢ` for the **actual** pointwise Kan colimit injections,
the action satisfies `ιᴿᵢ(a) • ιᴹᵢ(m) = ιᴹᵢ(a • m)` for all `a : R(V)` and
`m : M(V)` at one neighborhood. `pointwise_smul_ι` and the conveniently
explicit `pointwiseSmul_eq` expose this equation. Use
`pointwise_jointly_surjective` to represent **any** scalar and section at
one common neighborhood; it returns the index, elements and both equalities.
`pointwiseModule f R M U` specifies the action as an instance, while
`pointwiseSmul f R M U r m` uses it without requiring a caller to choose an
instance. No global instance is installed for arbitrary sites or unrelated
ring/module presheaves.

For a restriction `g : op U ⟶ op V`, `ring_map_ι` and `group_map_ι` identify
the genuine Kan restriction on generators. `restriction_smul` proves
`M'(g)(r • m) = R'(g)(r) • M'(g)(m)` for **every** coefficient `r` and section
`m`, by using common representatives, not only `r = 1`. The bundled
`inverseImageModule` is a native `PresheafOfModules` over `R'`; its restriction
identity/composition laws use the actual Kan additive functor.

## Maps, unit, comparison

For `φ : M ⟶ N`, `pointwiseMap f φ` applies `φ` to each section generator;
`pointwiseMap_ι` is its generator equation. `pointwiseMap_smul` establishes
linearity for every scalar in the Kan ring. `inverseImageMap f φ` bundles that
map as a native module-presheaf morphism; `inverseImageFunctor f R` supplies
objects/maps and proves identity and composition. `pointwiseMap_id` and
`pointwiseMap_comp` expose the additive laws directly.

The actual `L.pointwiseLeftKanExtensionUnit` on an open of `Y` sends a
section into the neighborhood indexed by the identity inclusion.
`unit_smul` proves that this **genuine** ring/module unit preserves the scalar
action for every coefficient; `pointwiseMap_unit` proves naturality in module
morphisms. The unit is not an assumed or separately chosen transformation.

`underlyingComparison f R` is a full natural isomorphism of additive
presheaf-valued functors:

```lean
inverseImageFunctor f R ⋙
    PresheafOfModules.toPresheaf (L.pointwiseLeftKanExtension R) ≅
  PresheafOfModules.toPresheaf R ⋙
    TopCat.Presheaf.pullback AddCommGrpCat f
```

Its components use the unique comparison from the pointwise left Kan
extension to the chosen presheaf pullback. `pointwiseToPullback_fac` shows
that this additive comparison composed with the actual pointwise Kan unit
equals the ordinary left Kan unit; naturality follows by the universal
property and the functor's `pointwiseMap_unit`. It is **only an additive
comparison**: no module over a chosen pulled-back ring is inferred from it.
There is no sheafification, CommRing-forgetful comparison, tensor product,
stalk statement or mixed-universe promise here.

## Reproduction and example clients

With the checked-in `lean-toolchain` and complete `lake-manifest.json`, run
`lake exe cache get` successfully **before** building. For the focused API,
run `lake --wfail build RingedSpaces.Modules.PresheafInverseImage
Test.PresheafInverseImage Test.PresheafInverseImageConcrete
Test.PresheafInverseImageRoot Test.PresheafInverseImageAxioms`, then
`lake --wfail build RingedSpaces` and `lake --wfail build`. The exact
direct/aggregate clients and axiom driver are in
`Test/PresheafInverseImage*.lean`; historical raw outputs are preserved in
the separate pre-release evidence archive.

`Test.PresheafInverseImage` proves named generic generator, common-index,
arbitrary-scalar restriction and map equations, identity/composition, actual
unit and additive-comparison naturality/unit. `Test.PresheafInverseImageRoot`
imports only the aggregate root and checks the same structure from downstream.
`Test.PresheafInverseImageConcrete` uses a nonidentity collapse map of the
two-point **discrete** space, integer ring and integer module with nonzero
input elements, and a restriction from the whole space to a proper **nonempty**
open. It also checks the empty space, empty open and zero ring `ZMod 1`;
constant presheaves may have sections on the empty open. These tests do not
assert that an arbitrary map's target colimit is nonzero or that the additive
comparison transports the coefficient ring.

The original contributors and the adapted research precursor are credited in
`NOTICE.md`. Native varying-ring colimits are provided by pinned mathlib.
