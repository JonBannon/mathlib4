/-
Copyright (c) 2025 Jon Bannon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon and Jireh Loreaux
-/
import Mathlib.Algebra.Group.Action.Opposite
import Mathlib.Algebra.Group.Action.Units
import Mathlib.Algebra.Group.Invertible.Defs
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Algebra.Ring.Aut
import Mathlib.Algebra.Ring.CompTypeclasses
import Mathlib.Algebra.Ring.Opposite
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.SetLike.Basic
import Mathlib.Algebra.Group.Star

/-!
# Star rings and modules

Write this.

-/

/-- A `*`-additive monoid `R` is an additive monoid with an involutive `star` operation which
preserves addition. -/
class StarAddMonoid (R : Type u) [AddMonoid R] extends InvolutiveStar R where
  /-- `star` commutes with addition -/
  star_add : ∀ r s : R, star (r + s) = star r + star s

export StarAddMonoid (star_add)

attribute [simp] star_add

/-- `star` as an `AddEquiv` -/
@[simps apply]
def starAddEquiv [AddMonoid R] [StarAddMonoid R] : R ≃+ R :=
  { InvolutiveStar.star_involutive.toPerm star with
    toFun := star
    map_add' := star_add }

variable (R) in
@[simp]
theorem star_zero [AddMonoid R] [StarAddMonoid R] : star (0 : R) = 0 :=
  (starAddEquiv : R ≃+ R).map_zero

@[simp]
theorem star_eq_zero [AddMonoid R] [StarAddMonoid R] {x : R} : star x = 0 ↔ x = 0 :=
  starAddEquiv.map_eq_zero_iff (M := R)

theorem star_ne_zero [AddMonoid R] [StarAddMonoid R] {x : R} : star x ≠ 0 ↔ x ≠ 0 := by
  simp only [ne_eq, star_eq_zero]

@[simp]
theorem star_neg [AddGroup R] [StarAddMonoid R] (r : R) : star (-r) = -star r :=
  (starAddEquiv : R ≃+ R).map_neg _

@[simp]
theorem star_sub [AddGroup R] [StarAddMonoid R] (r s : R) : star (r - s) = star r - star s :=
  (starAddEquiv : R ≃+ R).map_sub _ _

@[simp]
theorem star_nsmul [AddMonoid R] [StarAddMonoid R] (n : ℕ) (x : R) : star (n • x) = n • star x :=
  (starAddEquiv : R ≃+ R).toAddMonoidHom.map_nsmul _ _

@[simp]
theorem star_zsmul [AddGroup R] [StarAddMonoid R] (n : ℤ) (x : R) : star (n • x) = n • star x :=
  (starAddEquiv : R ≃+ R).toAddMonoidHom.map_zsmul _ _

/-- A `*`-ring `R` is a non-unital, non-associative (semi)ring with an involutive `star` operation
which is additive which makes `R` with its multiplicative structure into a `*`-multiplication
(i.e. `star (r * s) = star s * star r`). -/
class StarRing (R : Type u) [NonUnitalNonAssocSemiring R] extends StarMul R where
  /-- `star` commutes with addition -/
  star_add : ∀ r s : R, star (r + s) = star r + star s

instance (priority := 100) StarRing.toStarAddMonoid [NonUnitalNonAssocSemiring R] [StarRing R] :
    StarAddMonoid R where
  star_add := StarRing.star_add

/-- `star` as a `RingEquiv` from `R` to `Rᵐᵒᵖ` -/
@[simps apply]
def starRingEquiv [NonUnitalNonAssocSemiring R] [StarRing R] : R ≃+* Rᵐᵒᵖ :=
  { starAddEquiv.trans (MulOpposite.opAddEquiv : R ≃+ Rᵐᵒᵖ), starMulEquiv with
    toFun := fun x => MulOpposite.op (star x) }

@[simp, norm_cast]
theorem star_natCast [NonAssocSemiring R] [StarRing R] (n : ℕ) : star (n : R) = n :=
  (congr_arg unop (map_natCast (starRingEquiv : R ≃+* Rᵐᵒᵖ) n)).trans (unop_natCast _)

@[simp]
theorem star_ofNat [NonAssocSemiring R] [StarRing R] (n : ℕ) [n.AtLeastTwo] :
    star (ofNat(n) : R) = ofNat(n) :=
  star_natCast _

section

@[simp, norm_cast]
theorem star_intCast [NonAssocRing R] [StarRing R] (z : ℤ) : star (z : R) = z :=
  (congr_arg unop <| map_intCast (starRingEquiv : R ≃+* Rᵐᵒᵖ) z).trans (unop_intCast _)

end

section CommSemiring

variable [CommSemiring R] [StarRing R]

/-- `star` as a ring automorphism, for commutative `R`. -/
@[simps apply]
def starRingAut : RingAut R := { starAddEquiv, starMulAut (R := R) with toFun := star }

variable (R) in
/-- `star` as a ring endomorphism, for commutative `R`. This is used to denote complex
conjugation, and is available under the notation `conj` in the locale `ComplexConjugate`.

Note that this is the preferred form (over `starRingAut`, available under the same hypotheses)
because the notation `E →ₗ⋆[R] F` for an `R`-conjugate-linear map (short for
`E →ₛₗ[starRingEnd R] F`) does not pretty-print if there is a coercion involved, as would be the
case for `(↑starRingAut : R →* R)`. -/
def starRingEnd : R →+* R := @starRingAut R _ _

@[inherit_doc]
scoped[ComplexConjugate] notation "conj" => starRingEnd _

/-- This is not a simp lemma, since we usually want simp to keep `starRingEnd` bundled.
For example, for complex conjugation, we don't want simp to turn `conj x`
into the bare function `star x` automatically since most lemmas are about `conj x`. -/
theorem starRingEnd_apply (x : R) : starRingEnd R x = star x := rfl

/- Porting note (https://github.com/leanprover-community/mathlib4/issues/11119): removed `simp` attribute due to report by linter:

simp can prove this:
  by simp only [RingHomCompTriple.comp_apply, RingHom.id_apply]
One of the lemmas above could be a duplicate.
If that's not the case try reordering lemmas or adding @[priority].
-/
-- @[simp]
theorem starRingEnd_self_apply (x : R) : starRingEnd R (starRingEnd R x) = x := star_star x

instance RingHom.involutiveStar {S : Type*} [NonAssocSemiring S] : InvolutiveStar (S →+* R) where
  toStar := { star := fun f => RingHom.comp (starRingEnd R) f }
  star_involutive := by
    intro
    ext
    simp only [RingHom.coe_comp, Function.comp_apply, starRingEnd_self_apply]

theorem RingHom.star_def {S : Type*} [NonAssocSemiring S] (f : S →+* R) :
    Star.star f = RingHom.comp (starRingEnd R) f := rfl

theorem RingHom.star_apply {S : Type*} [NonAssocSemiring S] (f : S →+* R) (s : S) :
    star f s = star (f s) := rfl

-- A more convenient name for complex conjugation
alias Complex.conj_conj := starRingEnd_self_apply

alias RCLike.conj_conj := starRingEnd_self_apply

open scoped ComplexConjugate

@[simp] lemma conj_trivial [TrivialStar R] (a : R) : conj a = a := star_trivial _

end CommSemiring

@[simp]
theorem star_inv₀ [GroupWithZero R] [StarMul R] (x : R) : star x⁻¹ = (star x)⁻¹ :=
  op_injective <| (map_inv₀ (starMulEquiv : R ≃* Rᵐᵒᵖ) x).trans (op_inv (star x)).symm

@[simp]
theorem star_zpow₀ [GroupWithZero R] [StarMul R] (x : R) (z : ℤ) : star (x ^ z) = star x ^ z :=
  op_injective <| (map_zpow₀ (starMulEquiv : R ≃* Rᵐᵒᵖ) x z).trans (op_zpow (star x) z).symm

/-- When multiplication is commutative, `star` preserves division. -/
@[simp]
theorem star_div₀ [CommGroupWithZero R] [StarMul R] (x y : R) : star (x / y) = star x / star y := by
  apply op_injective
  rw [division_def, op_div, mul_comm, star_mul, star_inv₀, op_mul, op_inv]

/-- Any commutative semiring admits the trivial `*`-structure.

See note [reducible non-instances].
-/
abbrev starRingOfComm {R : Type*} [CommSemiring R] : StarRing R :=
  { starMulOfComm with
    star_add := fun _ _ => rfl }

instance Nat.instStarRing : StarRing ℕ := starRingOfComm
instance Int.instStarRing : StarRing ℤ := starRingOfComm
instance Nat.instTrivialStar : TrivialStar ℕ := ⟨fun _ ↦ rfl⟩
instance Int.instTrivialStar : TrivialStar ℤ := ⟨fun _ ↦ rfl⟩

/-- A star module `A` over a star ring `R` is a module which is a star add monoid,
and the two star structures are compatible in the sense
`star (r • a) = star r • star a`.

Note that it is up to the user of this typeclass to enforce
`[Semiring R] [StarRing R] [AddCommMonoid A] [StarAddMonoid A] [Module R A]`, and that
the statement only requires `[Star R] [Star A] [SMul R A]`.

If used as `[CommRing R] [StarRing R] [Semiring A] [StarRing A] [Algebra R A]`, this represents a
star algebra.
-/
class StarModule (R : Type u) (A : Type v) [Star R] [Star A] [SMul R A] : Prop where
  /-- `star` commutes with scalar multiplication -/
  star_smul : ∀ (r : R) (a : A), star (r • a) = star r • star a

export StarModule (star_smul)

attribute [simp] star_smul

/-- A commutative star monoid is a star module over itself via `Monoid.toMulAction`. -/
instance StarMul.toStarModule [CommMonoid R] [StarMul R] : StarModule R R :=
  ⟨star_mul'⟩

instance StarAddMonoid.toStarModuleNat {α} [AddCommMonoid α] [StarAddMonoid α] :
    StarModule ℕ α where star_smul := star_nsmul

instance StarAddMonoid.toStarModuleInt {α} [AddCommGroup α] [StarAddMonoid α] : StarModule ℤ α where
  star_smul := star_zsmul

namespace RingHomInvPair

/-- Instance needed to define star-linear maps over a commutative star ring
(ex: conjugate-linear maps when R = ℂ). -/
instance [CommSemiring R] [StarRing R] : RingHomInvPair (starRingEnd R) (starRingEnd R) :=
  ⟨RingHom.ext star_star, RingHom.ext star_star⟩

end RingHomInvPair

section

/-- `StarHomClass F R S` states that `F` is a type of `star`-preserving maps from `R` to `S`. -/
class StarHomClass (F : Type*) (R S : outParam Type*) [Star R] [Star S] [FunLike F R S] : Prop where
  /-- the maps preserve star -/
  map_star : ∀ (f : F) (r : R), f (star r) = star (f r)

export StarHomClass (map_star)

end
