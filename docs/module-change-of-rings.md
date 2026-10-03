# Same-site change of rings for modules

This library constructs extension of scalars along a full map of
commutative-ring presheaves on an arbitrary category, then extends it to
module sheaves on a site. It uses mathlib's module-category scalar extension,
restriction, tensor Hom equivalence and module sheafification; it does not
implement a second tensor-product quotient.

## Presheaves

Let `C` be a category, `A B : Cᵒᵖ ⥤ CommRingCat.{u}` and
`theta : A ⟶ B`. The map `theta` is a natural transformation **of the whole
presheaves**, not merely a family of pointwise ring maps. A module presheaf
`M : PresheafOfModulesOfCommRing.{u} A` has `A(U)`-modules `M(U)` and semilinear
restriction maps. The result `tensorPresheaf A B theta M` has underlying
`B(U)`-module

```text
B(U) ⊗[A(U), theta_U] M(U).
```

Native `ModuleCat.extendScalars` supplies the tensor and its unit
`m ↦ 1 ⊗ m`; native `ModuleCat.extendRestrictScalarsAdj` supplies the
pointwise tensor Hom equivalence. For a site arrow `f : U ⟶ V`, define the
restriction by the mate of `m ↦ 1 ⊗ M(f)(m)`. This is `A(U)`-linear: the
semilinear restrictions and naturality of `theta` give

```text
theta_V(A(f)(a)) = B(f)(theta_U(a)).
```

The result is `B(U)`-linear into the module obtained by restricting scalars
along `B(f)`. Thus `tensorRestriction_smul` asserts on *every* scalar `b`:

```text
restriction_f(b • (1 ⊗ m)) = B(f)(b) • (1 ⊗ M(f)(m)).
```

Native `ModuleCat.ExtendScalars.hom_ext` reduces identity, composition and
map naturality to these unit equations. The same reduction proves the
functor `tensorPresheafFunctor A B theta`. The two maps of its natural Hom
equivalence send `t` to `m ↦ t(1 ⊗ m)` and `g` to the native linear
extension `b ⊗ m ↦ b • g(m)`; the latter holds for arbitrary `b` in
`tensorPresheafHomUp_smul`. Both composites are identity on Hom objects,
and `tensorPresheafHomDown_naturality_left/right` prove naturality. Hence
`tensorPresheafAdjunction` is an actual adjunction, with unit and counit
equations given by `tensorPresheafAdjunction_unit/counit`.

No topology, cover, sheaf condition, small-category constraint, nonempty
category or nonzero-ring assumption enters this layer. `C : Type u₁` and
`Category.{v₁} C` are independent; coefficient rings and module carriers
both use universe `u`.

## Sheaves

Let `J : GrothendieckTopology C` and
`A B : Sheaf J CommRingCat.{u}`. To forget a commutative-ring sheaf to
`RingCat`, the generic layer explicitly assumes
`J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})`. Native module
sheafification additionally requires both
`HasWeakSheafify J AddCommGrpCat.{u}` and
`J.WEqualsLocallyBijective AddCommGrpCat.{u}`. The comparison from
`(ringSheaf B).obj` to itself is the identity, whose local injectivity and
surjectivity follow from its invertibility. None of these sheafification
witnesses is postulated for an arbitrary site.

Define `tensorSheafFunctor` by forgetting a sheaf of `A`-modules to a
presheaf, applying the tensor-presheaf functor, and applying native
`PresheafOfModules.sheafification (𝟙 (ringSheaf B).obj)`. For a sheaf `N`
of `B`-modules, compose native sheafification Hom equivalence, the proven
presheaf tensor Hom equivalence, and fully faithful forgetting from sheaves
of modules. `tensorSheafHomEquiv_naturality_left/right` prove this composite
natural, yielding `tensorSheafAdjunction` to restriction of scalars along
`ringSheafMap A B theta`—the full morphism of ring sheaves.

The sheafification unit `j` is a map from the **tensor presheaf** into the
underlying presheaf of the sheafification. On a section `m` of `M` the
adjunction unit is `j(1 ⊗ m)`; for the counit at `N`, the equation on
generators is

```text
ε_N(j(b ⊗ n)) = b • n.
```

The second equality is established via both natural Hom equivalences,
not by identifying arbitrary sheaf sections with tensors. These equations
are `tensorSheafAdjunction_unit/counit`, with the sheaf Hom evaluation also
available as `tensorSheafHomEquiv_apply`. Equalities concern arbitrary
scalars on **sheafification-unit generators** only. An arbitrary open
section of a sheafified tensor presheaf need only be locally represented.

For `X : TopCat.{u}`, `opensWeakSheafify X` and
`opensWEqualsLocallyBijective X` obtain the genuine mathlib topological
instances; the ring-sheaf composition instance comes from mathlib's
limit-preserving forgetful functor. `opensTensorSheafAdjunction` provides the
diagonal topological client, including empty spaces and zero rings. No
mixed ring/module/topological universes or arbitrary-base inverse image,
affine-localization, stalk or quasi-coherent comparison is claimed.
The native chosen categorical pullback is intentionally **not exported or
identified** with this explicit extension; no consumer requires that extra
comparison and the explicit adjunction already supplies the needed universal
property without a `SmallCategory` premise.

## Clients and attribution

`RingedSpacesTests/ModuleChangeOfRings.lean` checks the direct import and actual
two-object arrow, zero ring, empty site/space, unit, counit, naturality and
Hom inverse clients. `RingedSpacesTests/ModuleChangeOfRingsRoot.lean` checks the
aggregate import; `RingedSpacesTests/ModuleChangeOfRingsAxioms.lean` prints transitive
axioms in the pinned environment. Contributor and adapted-research credit
is in `NOTICE.md`. Fetch the matching mathlib cache with `lake exe cache get`
before running `lake --wfail build`.
