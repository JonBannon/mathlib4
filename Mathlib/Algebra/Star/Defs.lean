/-
Copyright (c) 2025 Jon Bannon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon and Jireh Loreaux
-/

import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.SetLike.Basic

/-!
# Basic Star defs, and Star rings and modules

Write this.

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

/-- `star` as an equivalence when it is involutive. -/
protected def Equiv.star [InvolutiveStar R] : Equiv.Perm R :=
  star_involutive.toPerm _

/-- Typeclass for a trivial star operation. This is mostly meant for `ℝ`.
-/
class TrivialStar (R : Type u) [Star R] : Prop where
  /-- Condition that star is trivial -/
  star_trivial : ∀ r : R, star r = r

export TrivialStar (star_trivial)

attribute [simp] star_trivial

/-- A `*`-magma is a magma `R` with an involutive operation `star`
such that `star (r * s) = star s * star r`.
-/
class StarMul (R : Type u) [Mul R] extends InvolutiveStar R where
  /-- `star` skew-distributes over multiplication. -/
  star_mul : ∀ r s : R, star (r * s) = star s * star r

export StarMul (star_mul)

attribute [simp 900] star_mul

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

/-- A `*`-ring `R` is a non-unital, non-associative (semi)ring with an involutive `star` operation
which is additive which makes `R` with its multiplicative structure into a `*`-multiplication
(i.e. `star (r * s) = star s * star r`). -/
class StarRing (R : Type u) [NonUnitalNonAssocSemiring R] extends StarMul R where
  /-- `star` commutes with addition -/
  star_add : ∀ r s : R, star (r + s) = star r + star s

instance (priority := 100) StarRing.toStarAddMonoid [NonUnitalNonAssocSemiring R] [StarRing R] :
    StarAddMonoid R where
  star_add := StarRing.star_add
