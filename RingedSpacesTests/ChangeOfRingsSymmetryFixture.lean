/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import RingedSpacesTests.ChangeOfRingsSymmetry
public import Mathlib.Data.Rat.Cast.Defs
public import Mathlib.Data.Rat.Lemmas

/-!
# A changing coefficient-ring restriction

The arrow from `1` to `0` takes integer coefficients to rational coefficients.
The natural map from the constant integers to this diagram is the identity at
`1`, and integer inclusion at `0`.
-/

@[expose] public section

open CategoryTheory RingedSpaces.Modules

namespace Test.ChangeOfRingsSymmetryFixture

private def arrow : Opposite.op (1 : Fin 2) ⟶ Opposite.op (0 : Fin 2) :=
  (homOfLE (by decide : (0 : Fin 2) ≤ 1)).op

/-- Integer coefficients at object `1`, rational coefficients at object `0`. -/
noncomputable def changingRing : (Fin 2)ᵒᵖ ⥤ CommRingCat where
  obj U := match U.unop with
    | 0 => CommRingCat.of ℚ
    | 1 => CommRingCat.of ℤ
  map {U V} f :=
    match U, V, f with
    | .op 0, .op 0, _ => 𝟙 (CommRingCat.of ℚ)
    | .op 0, .op 1, h => False.elim (by
        have hf := h.unop.le
        simp at hf)
    | .op 1, .op 0, _ => CommRingCat.ofHom (Int.castRingHom ℚ)
    | .op 1, .op 1, _ => 𝟙 (CommRingCat.of ℤ)
  map_id U := by
    cases U with | op first =>
      cases first using Fin.cases with
      | zero => rfl
      | succ second => cases second using Fin.cases with
        | zero => rfl
        | succ impossible => exact Fin.elim0 impossible
  map_comp {U V W} f g := by
    cases U with | op first =>
      cases V with | op second =>
        cases W with | op third =>
          cases first using Fin.cases with
          | zero =>
              cases second using Fin.cases with
              | zero =>
                  cases third using Fin.cases with
                  | zero => rfl
                  | succ impossible => exact False.elim (by
                      have hg := g.unop.le
                      simp at hg)
              | succ impossible => exact False.elim (by
                  have hf := f.unop.le
                  simp at hf)
          | succ first =>
              cases first using Fin.cases with
              | succ impossible => exact Fin.elim0 impossible
              | zero =>
                  cases second using Fin.cases with
                  | zero =>
                      cases third using Fin.cases with
                      | zero => rfl
                      | succ impossible => exact False.elim (by
                          have hg := g.unop.le
                          simp at hg)
                  | succ second =>
                      cases second using Fin.cases with
                      | succ impossible => exact Fin.elim0 impossible
                      | zero =>
                          cases third using Fin.cases with
                          | zero => rfl
                          | succ third =>
                              cases third using Fin.cases with
                              | zero => rfl
                              | succ impossible => exact Fin.elim0 impossible

/-- The constant integer source ring presheaf. -/
noncomputable def constantIntegers : (Fin 2)ᵒᵖ ⥤ CommRingCat :=
  (Functor.const (Fin 2)ᵒᵖ).obj (CommRingCat.of ℤ)

/-- Identity at object `1` and integer inclusion into rationals at object `0`. -/
noncomputable def integerInclusion : constantIntegers ⟶ changingRing where
  app U := by
    cases U with | op first =>
      cases first using Fin.cases with
      | zero => exact CommRingCat.ofHom (Int.castRingHom ℚ)
      | succ second => cases second using Fin.cases with
        | zero => exact 𝟙 (CommRingCat.of ℤ)
        | succ impossible => exact Fin.elim0 impossible
  naturality {U V} f := by
    cases U with | op first =>
      cases V with | op second =>
        cases first using Fin.cases with
        | zero =>
            cases second using Fin.cases with
            | zero => rfl
            | succ impossible => exact False.elim (by
                have hf := f.unop.le
                simp at hf)
        | succ first =>
            cases first using Fin.cases with
            | succ impossible => exact Fin.elim0 impossible
            | zero =>
                cases second using Fin.cases with
                | zero => rfl
                | succ second =>
                    cases second using Fin.cases with
                    | zero => rfl
                    | succ impossible => exact Fin.elim0 impossible

private theorem varyingRestrictionOnTwo :
    changingRing.map arrow (2 : changingRing.obj (Opposite.op 1)) =
      (2 : changingRing.obj (Opposite.op 0)) := by
  change (Int.castRingHom ℚ) 2 = 2
  simp

theorem nonidentityComponentOnTwo :
    integerInclusion.app (Opposite.op 0)
        (2 : constantIntegers.obj (Opposite.op 0)) =
      (2 : changingRing.obj (Opposite.op 0)) := by
  change (Int.castRingHom ℚ) 2 = 2
  simp

/-- The coefficient component at object `0` genuinely changes rings: it omits `1/2`. -/
theorem integerInclusionNotSurjective :
    ¬ Function.Surjective ((integerInclusion.app (Opposite.op (0 : Fin 2))).hom) := by
  intro hsurj
  obtain ⟨integer, hinteger⟩ := hsurj (1 / 2 : ℚ)
  have hden : (1 / 2 : ℚ).den = 1 := by
    change (Int.castRingHom ℚ) (integer : ℤ) = (1 / 2 : ℚ) at hinteger
    have hsource : ((Int.castRingHom ℚ) (integer : ℤ)).den = 1 := by
      simpa [Int.castRingHom] using (Rat.den_intCast (integer : ℤ))
    exact (congrArg Rat.den hinteger).symm.trans hsource
  have hdiv : (2 : ℕ) ∣ 1 :=
    (Rat.den_div_natCast_eq_one_iff 1 2 (by decide)).mp hden
  exact (by decide : ¬ (2 : ℕ) ∣ 1) hdiv

theorem nontrivialTwoCoefficientRestriction (M : Presheaves constantIntegers)
    (m : M.obj (Opposite.op (1 : Fin 2))) :
    (rightPresheaf constantIntegers changingRing integerInclusion M).map
        (homOfLE (by decide : (0 : Fin 2) ≤ 1)).op
        (rightSectionSmul constantIntegers changingRing integerInclusion M
          (Opposite.op 1) 3
          (rightPure constantIntegers changingRing integerInclusion M
            (Opposite.op 1) m 2)) =
      rightSectionSmul constantIntegers changingRing integerInclusion M (Opposite.op 0)
        (3 : ℚ)
        (rightPure constantIntegers changingRing integerInclusion M (Opposite.op 0)
          (M.map (homOfLE (by decide : (0 : Fin 2) ≤ 1)).op m) (2 : ℚ)) := by
  change rightRestriction constantIntegers changingRing integerInclusion M arrow
    (rightSectionSmul constantIntegers changingRing integerInclusion M
      (Opposite.op 1) 3
      (rightPure constantIntegers changingRing integerInclusion M (Opposite.op 1) m 2)) = _
  rw [rightRestriction_semilinear, rightRestriction_pure]
  have hthree : changingRing.map arrow (3 : changingRing.obj (Opposite.op 1)) =
      (3 : changingRing.obj (Opposite.op 0)) := by
    change (Int.castRingHom ℚ) 3 = 3
    simp
  rw [varyingRestrictionOnTwo, hthree]
  rfl

private theorem nontrivialTwoCoefficientRestriction_original (M : Presheaves constantIntegers)
    (m : M.obj (Opposite.op (1 : Fin 2))) :
    (rightPresheaf constantIntegers changingRing integerInclusion M).map arrow
        (rightSectionSmul constantIntegers changingRing integerInclusion M
          (Opposite.op 1) 3
          (rightPure constantIntegers changingRing integerInclusion M
            (Opposite.op 1) m 2)) =
      rightSectionSmul constantIntegers changingRing integerInclusion M (Opposite.op 0)
        (3 : ℚ)
        (rightPure constantIntegers changingRing integerInclusion M (Opposite.op 0)
          (M.map arrow m) (2 : ℚ)) :=
  nontrivialTwoCoefficientRestriction M m

end Test.ChangeOfRingsSymmetryFixture

#lint-
