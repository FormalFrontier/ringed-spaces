# Right-factor scalar extension and tensor symmetry

Vakil's *The Rising Sea: Foundations of Algebraic Geometry* (21 October 2025
draft), §2.6.4 and Exercise 2.6.K(a) (p. 92), motivate forming the tensor
presheaf before sheafifying it. The right-factor order, tensor symmetry and
arbitrary-site comparison are project prerequisites for Exercise 7.2.D(b,c,e)
(p. 205), not separate theorems in the source. In particular the sheafified
right tensor is not identified with raw tensors on each open.

## Statement and hypotheses

Fix any category `C : Type u₁` with `Category.{v₁} C`; these universes are
independent. Let `A B : Cᵒᵖ ⥤ CommRingCat.{u}`, let `theta : A ⟶ B` be a
natural transformation **of the entire presheaves**, and let `M` be a
presheaf of `A`-modules. Coefficient rings and module carriers share universe
`u`. No site, smallness, nonemptiness, nonzero-ring, flatness or finiteness
hypothesis is needed at this level. On an object `U` set `R=A(U)`, `S=B(U)`
and `φ=theta_U : R →+* S`. The right factor `S` is an `R`-module by
`a • b = φ(a)b`, using *the actual component* of `theta`.

`rightSection A B theta M U` is the genuine tensor

```text
M(U) ⊗_[R, φ] S,
```

not an alias for the opposite-order tensor. `rightSectionCat` bundles its
transported `S`-module structure. The existing `tensorSection` has carrier
`S ⊗_[R] M(U)` and its native `S`-module action. The `S`-linear
`rightSectionIso` sends `m ⊗ b` to `b ⊗ m`, with inverse `b ⊗ m ↦ m ⊗ b`.
`rightPresheafNatIso` compares whole **functors** on `A`-module presheaves;
the source functor's objects are actual right-factor tensors.

## Proof and sectionwise laws

The native `ModuleCat.restrictScalars` constructs the coefficient action on
the right factor. The native `TensorProduct.comm` is additive and `R`-linear;
transport the already existing `S`-module structure on `S ⊗_[R] M(U)` along
its additive equivalence, with `AddEquiv.module`. Consequently commutation is
an `S`-linear module isomorphism. Its pure-tensor equations are native
`TensorProduct.comm_tmul` and `comm_symm_tmul`.

In the transported action, for **arbitrary** `b,c : S` and `m : M(U)`:

```text
c • (m ⊗ b) = m ⊗ (c*b),
(a • m) ⊗ b = m ⊗ (φ(a)*b).
```

The first follows by injecting the equation through the `S`-linear symmetry
and applying the native scalar action on `S ⊗_[R] M(U)`; the second is the
tensor balancing relation with the `φ`-restricted right factor. The original
tensor also has its native `R`-action. The theorem `theta_smul` proves, on
**every tensor** `t`, that `a •_R t = φ(a) •_S t`. Tensor induction reduces
this equality to the two displayed pure-tensor equations; distributivity
handles sums. This proof does not add any assumed scalar-tower structure.

For any arrow `f : U ⟶ V` in `Cᵒᵖ`, conjugate the existing restriction
`tensorRestriction` by the section isomorphisms. The resulting
`rightRestriction` is linear as a map to the `B(f)`-restricted target, so it
is semilinear on **all** tensors and coefficients, not only generators:

```text
res_f(m ⊗ b) = M(f)(m) ⊗ B(f)(b),
res_f(c • t) = B(f)(c) • res_f(t).
```

This follows directly from the existing opposite-order restriction formula
`tensorRestriction_smul` and the inverse symmetry equation. Transport its
identity and composition through the isomorphism to obtain the actual
presheaf `rightPresheaf`, and use `PresheafOfModulesOfCommRing.isoMk` to
obtain `rightPresheafIso`. For a morphism `h : M ⟶ N`, conjugating
`tensorPresheafMap` produces `rightPresheafMap` with
`m ⊗ b ↦ h_U(m) ⊗ b`. Naturality of the existing map transfers its
restriction square; conjugation transfers the functor identity and
composition laws. The component isomorphisms form `rightPresheafNatIso`.

The unit `rightPresheafUnit` is `m ↦ m ⊗ 1` and its comparison is the
existing `presheafTensorUnit`. A consumer obtains the formula
`m ⊗ b ↦ b • g_U(m)` by composing `rightPresheafIso.hom` with the **existing**
`tensorPresheafHomUp` and applying `tensorPresheafHomUp_smul`; there is no
second Hom-equivalence or scalar adjunction here.

## Sheafification

For any Grothendieck topology `J` and commutative-ring sheaves `A,B`, use
**exactly** the existing witnesses
`J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})`,
`HasWeakSheafify J AddCommGrpCat.{u}` and
`J.WEqualsLocallyBijective AddCommGrpCat.{u}`. First forget an `A`-module
sheaf to a presheaf, apply `rightPresheafFunctor`, then apply the existing
`moduleSheafification B`. Whiskering the proven presheaf natural iso by
these two functors gives `rightSheafNatIso` to the existing
`tensorSheafFunctor`. Naturality of the **actual sheafification-adjunction
unit** proves `rightSheafificationUnit_naturality`: comparing presheaf tensors
before sheafification equals first sheafifying and applying the induced sheaf
isomorphism. An arbitrary-open section of the resulting sheaf is **not**
identified with a raw tensor.

On the diagonal topological open site, `opensRightSheafNatIso` obtains both
native weak-sheafification witnesses from `opensWeakSheafify` and
`opensWEqualsLocallyBijective`. No arbitrary-site witnesses are fabricated.
There is no chosen native-pullback comparison and no rebuilt sheaf Hom or
adjunction in this contribution.

## Downstream examples and reproducibility

`RingedSpacesTests/ChangeOfRingsSymmetry.lean` directly imports both leaves and exercises
arbitrary universes, scalars, tensors, full-map balancing, all-tensor
compatibility, units, restrictions, naturality, and the existing Hom formula.
`RingedSpacesTests/ChangeOfRingsSymmetryFixture.lean` defines a literal two-object
diagram with `B(1)=ℤ`, `B(0)=ℚ`, and `B(1→0)=Int.castRingHom ℚ`, while `A`
is constant `ℤ` and `theta_1=id`, `theta_0=Int.castRingHom ℚ`.
`integerInclusionNotSurjective` proves that `1/2` is outside the image of
`theta_0`, using the denominator of an integer rational; thus `theta` is
genuinely nonidentity. The clients restrict nonzero coefficients `2,3` along
the nonidentity arrow,
not merely along an identity or between constant coefficient rings.
`RingedSpacesTests/ChangeOfRingsSymmetryRoot.lean` checks the aggregate import on the
**discrete** two-point space (`⊥` in mathlib's reverse inclusion order for
topologies). Its original open inclusion is from the empty open to the whole
space; the associated section restriction is from the whole space to the empty
open. The zero-ring and empty-space boundary tests remain. The additional
open `{0}` is proved nonempty and proper; the concrete integer skyscraper
ring at `0` and its rank-one module have a proved nonzero global input `1`.
The client restricts the genuine right-factor tensor `1 ⊗ 1` from the whole
space to `{0}`, compares its image through the production presheaf isomorphism,
and applies the actual sheafification-unit square at `{0}` to this restricted
input. This does **not** claim the tensor or its sheafification image is nonzero.
The direct clients separately exercise zero coefficient rings and an empty
site; the topological client discharges the native witnesses even for an empty
open.

`RingedSpacesTests/ChangeOfRingsSymmetryAxioms.lean` is an axiom-audit client. Fetch the
matching precompiled mathlib cache with `lake exe cache get` before running
`lake --wfail build`. Contributor and source-adaptation credit is in
`NOTICE.md`; historical raw logs and review records are preserved separately
from this mathematical guide in the pre-release evidence archive.
