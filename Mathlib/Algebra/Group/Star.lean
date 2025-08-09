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
import Mathlib.Algebra.Star.Defs

/-!
# Star monoids

Write this.

-/

universe u v w

variable {R : Type u}

open MulOpposite

/-- `star` as a `MulEquiv` from `R` to `Rᵐᵒᵖ` -/
@[simps apply]
def starMulEquiv [Mul R] [StarMul R] : R ≃* Rᵐᵒᵖ :=
  { (InvolutiveStar.star_involutive.toPerm star).trans opEquiv with
    toFun := fun x => MulOpposite.op (star x)
    map_mul' := fun x y => by simp only [star_mul, op_mul] }

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

/-- In a commutative ring, make `simp` prefer leaving the order unchanged. -/
@[simp]
theorem star_mul' [CommMagma R] [StarMul R] (x y : R) : star (x * y) = star x * star y :=
  (star_mul x y).trans (mul_comm _ _)

/-- `star` as a `MulAut` for commutative `R`. -/
@[simps apply]
def starMulAut [CommSemigroup R] [StarMul R] : MulAut R :=
  { InvolutiveStar.star_involutive.toPerm star with
    toFun := star
    map_mul' := star_mul' }

variable (R) in
@[simp]
theorem star_one [MulOneClass R] [StarMul R] : star (1 : R) = 1 :=
  op_injective <| (starMulEquiv : R ≃* Rᵐᵒᵖ).map_one.trans op_one.symm

@[simp]
theorem star_pow [Monoid R] [StarMul R] (x : R) (n : ℕ) : star (x ^ n) = star x ^ n :=
  op_injective <|
    ((starMulEquiv : R ≃* Rᵐᵒᵖ).toMonoidHom.map_pow x n).trans (op_pow (star x) n).symm

@[simp]
theorem star_inv [Group R] [StarMul R] (x : R) : star x⁻¹ = (star x)⁻¹ :=
  op_injective <| ((starMulEquiv : R ≃* Rᵐᵒᵖ).toMonoidHom.map_inv x).trans (op_inv (star x)).symm

@[simp]
theorem star_zpow [Group R] [StarMul R] (x : R) (z : ℤ) : star (x ^ z) = star x ^ z :=
  op_injective <|
    ((starMulEquiv : R ≃* Rᵐᵒᵖ).toMonoidHom.map_zpow x z).trans (op_zpow (star x) z).symm

/-- When multiplication is commutative, `star` preserves division. -/
@[simp]
theorem star_div [CommGroup R] [StarMul R] (x y : R) : star (x / y) = star x / star y :=
  map_div (starMulAut : R ≃* R) _ _


--below this line, all ring stuff from Basic, but over there containing some breakage:

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

/-! ### Instances -/


namespace Units

variable [Monoid R] [StarMul R]

instance : StarMul Rˣ where
  star u :=
    { val := star u
      inv := star ↑u⁻¹
      val_inv := (star_mul _ _).symm.trans <| (congr_arg star u.inv_val).trans <| star_one _
      inv_val := (star_mul _ _).symm.trans <| (congr_arg star u.val_inv).trans <| star_one _ }
  star_involutive _ := Units.ext (star_involutive _)
  star_mul _ _ := Units.ext (star_mul _ _)

@[simp]
theorem coe_star (u : Rˣ) : ↑(star u) = (star ↑u : R) :=
  rfl

@[simp]
theorem coe_star_inv (u : Rˣ) : ↑(star u)⁻¹ = (star ↑u⁻¹ : R) :=
  rfl

instance {A : Type*} [Star A] [SMul R A] [StarModule R A] : StarModule Rˣ A :=
  ⟨fun u a => star_smul (u : R) a⟩

end Units

protected theorem IsUnit.star [Monoid R] [StarMul R] {a : R} : IsUnit a → IsUnit (star a)
  | ⟨u, hu⟩ => ⟨Star.star u, hu ▸ rfl⟩

@[simp]
theorem isUnit_star [Monoid R] [StarMul R] {a : R} : IsUnit (star a) ↔ IsUnit a :=
  ⟨fun h => star_star a ▸ h.star, IsUnit.star⟩

theorem Ring.inverse_star [Semiring R] [StarRing R] (a : R) :
    Ring.inverse (star a) = star (Ring.inverse a) := by
  by_cases ha : IsUnit a
  · obtain ⟨u, rfl⟩ := ha
    rw [Ring.inverse_unit, ← Units.coe_star, Ring.inverse_unit, ← Units.coe_star_inv]
  rw [Ring.inverse_non_unit _ ha, Ring.inverse_non_unit _ (mt isUnit_star.mp ha), star_zero]

protected instance Invertible.star {R : Type*} [MulOneClass R] [StarMul R] (r : R) [Invertible r] :
    Invertible (star r) where
  invOf := Star.star (⅟r)
  invOf_mul_self := by rw [← star_mul, mul_invOf_self, star_one]
  mul_invOf_self := by rw [← star_mul, invOf_mul_self, star_one]

theorem star_invOf {R : Type*} [Monoid R] [StarMul R] (r : R) [Invertible r]
    [Invertible (star r)] : star (⅟r) = ⅟(star r) := by
  have : star (⅟r) = star (⅟r) * ((star r) * ⅟(star r)) := by
    simp only [mul_invOf_self, mul_one]
  rw [this, ← mul_assoc]
  have : (star (⅟r)) * (star r) = star 1 := by rw [← star_mul, mul_invOf_self]
  rw [this, star_one, one_mul]


section Regular

protected theorem IsLeftRegular.star [Mul R] [StarMul R] {x : R} (hx : IsLeftRegular x) :
    IsRightRegular (star x) :=
  fun a b h => star_injective <| hx <| by simpa using congr_arg Star.star h

protected theorem IsRightRegular.star [Mul R] [StarMul R] {x : R} (hx : IsRightRegular x) :
    IsLeftRegular (star x) :=
  fun a b h => star_injective <| hx <| by simpa using congr_arg Star.star h

protected theorem IsRegular.star [Mul R] [StarMul R] {x : R} (hx : IsRegular x) :
    IsRegular (star x) :=
  ⟨hx.right.star, hx.left.star⟩

@[simp]
theorem isRightRegular_star_iff [Mul R] [StarMul R] {x : R} :
    IsRightRegular (star x) ↔ IsLeftRegular x :=
  ⟨fun h => star_star x ▸ h.star, (·.star)⟩

@[simp]
theorem isLeftRegular_star_iff [Mul R] [StarMul R] {x : R} :
    IsLeftRegular (star x) ↔ IsRightRegular x :=
  ⟨fun h => star_star x ▸ h.star, (·.star)⟩

@[simp]
theorem isRegular_star_iff [Mul R] [StarMul R] {x : R} :
    IsRegular (star x) ↔ IsRegular x := by
  rw [isRegular_iff, isRegular_iff, isRightRegular_star_iff, isLeftRegular_star_iff, and_comm]

end Regular


namespace MulOpposite

/-- The opposite type carries the same star operation. -/
instance [Star R] : Star Rᵐᵒᵖ where star r := op (star r.unop)

@[simp]
theorem unop_star [Star R] (r : Rᵐᵒᵖ) : unop (star r) = star (unop r) :=
  rfl

@[simp]
theorem op_star [Star R] (r : R) : op (star r) = star (op r) :=
  rfl

instance [InvolutiveStar R] : InvolutiveStar Rᵐᵒᵖ where
  star_involutive r := unop_injective (star_star r.unop)

instance [Mul R] [StarMul R] : StarMul Rᵐᵒᵖ where
  star_mul x y := unop_injective (star_mul y.unop x.unop)

instance [AddMonoid R] [StarAddMonoid R] : StarAddMonoid Rᵐᵒᵖ where
  star_add x y := unop_injective (star_add x.unop y.unop)

instance [NonUnitalSemiring R] [StarRing R] : StarRing Rᵐᵒᵖ where
  star_add x y := unop_injective (star_add x.unop y.unop)

instance {M : Type*} [Star R] [Star M] [SMul R M] [StarModule R M] :
    StarModule R Mᵐᵒᵖ where
  star_smul r x := unop_injective (star_smul r x.unop)

end MulOpposite

/-- A commutative star monoid is a star module over its opposite via
`Monoid.toOppositeMulAction`. -/
instance StarSemigroup.toOpposite_starModule [CommMonoid R] [StarMul R] :
    StarModule Rᵐᵒᵖ R :=
  ⟨fun r s => star_mul' s r.unop⟩
