/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
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

/-!
# Star monoids, rings, and modules

We introduce the basic algebraic notions of star monoids, star rings, and star modules.
A star algebra is simply a star ring that is also a star module.

These are implemented as "mixin" typeclasses, so to summon a star ring (for example)
one needs to write `(R : Type*) [Ring R] [StarRing R]`.
This avoids difficulties with diamond inheritance.

For now we simply do not introduce notations,
as different users are expected to feel strongly about the relative merits of
`r^*`, `r†`, `rᘁ`, and so on.

Our star rings are actually star non-unital, non-associative, semirings, but of course we can prove
`star_neg : star (-r) = - star r` when the underlying semiring is a ring.
-/

assert_not_exists Finset Subgroup Rat.instField

universe u v w

open MulOpposite

variable {R : Type u}

export Star (star)

/-- `StarMemClass S G` states `S` is a type of subsets `s ⊆ G` closed under star. -/
class StarMemClass (S R : Type*) [Star R] [SetLike S R] : Prop where
  /-- Closure under star. -/
  star_mem : ∀ {s : S} {r : R}, r ∈ s → star r ∈ s

export StarMemClass (star_mem)

attribute [aesop 90% (rule_sets := [SetLike])] star_mem

namespace StarMemClass

variable {S : Type w} [Star R] [SetLike S R] [hS : StarMemClass S R] (s : S)

instance instStar : Star s where
  star r := ⟨star (r : R), star_mem r.prop⟩

@[simp] lemma coe_star (x : s) : star x = star (x : R) := rfl

end StarMemClass

/-- Typeclass for a star operation with is involutive.
-/
class InvolutiveStar (R : Type u) extends Star R where
  /-- Involutive condition. -/
  star_involutive : Function.Involutive star

export InvolutiveStar (star_involutive)

@[simp]
theorem star_star [InvolutiveStar R] (r : R) : star (star r) = r :=
  star_involutive _

lemma star_mem_iff {S : Type*} [SetLike S R] [InvolutiveStar R] [StarMemClass S R]
    {s : S} {x : R} : star x ∈ s ↔ x ∈ s :=
  ⟨fun h => star_star x ▸ star_mem h, fun h => star_mem h⟩

theorem star_injective [InvolutiveStar R] : Function.Injective (star : R → R) :=
  Function.Involutive.injective star_involutive

@[aesop 5% (rule_sets := [SetLike!])]
theorem mem_of_star_mem {S R : Type*} [InvolutiveStar R] [SetLike S R] [StarMemClass S R]
    {s : S} {r : R} (hr : star r ∈ s) : r ∈ s := by rw [← star_star r]; exact star_mem hr

@[simp]
theorem star_inj [InvolutiveStar R] {x y : R} : star x = star y ↔ x = y :=
  star_injective.eq_iff

/-- `star` as an equivalence when it is involutive. -/
protected def Equiv.star [InvolutiveStar R] : Equiv.Perm R :=
  star_involutive.toPerm _

theorem eq_star_of_eq_star [InvolutiveStar R] {r s : R} (h : r = star s) : s = star r := by
  simp [h]

theorem eq_star_iff_eq_star [InvolutiveStar R] {r s : R} : r = star s ↔ s = star r :=
  ⟨eq_star_of_eq_star, eq_star_of_eq_star⟩

theorem star_eq_iff_star_eq [InvolutiveStar R] {r s : R} : star r = s ↔ star s = r :=
  eq_comm.trans <| eq_star_iff_eq_star.trans eq_comm

/-- Typeclass for a trivial star operation. This is mostly meant for `ℝ`.
-/
class TrivialStar (R : Type u) [Star R] : Prop where
  /-- Condition that star is trivial -/
  star_trivial : ∀ r : R, star r = r

export TrivialStar (star_trivial)

attribute [simp] star_trivial

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
