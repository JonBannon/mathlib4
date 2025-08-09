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
import Mathlib.Algebra.Star.Basic

/-!
# Star monoids

Write this.

-/

universe u v w

open MulOpposite

variable {R : Type u}

/-- A `*`-magma is a magma `R` with an involutive operation `star`
such that `star (r * s) = star s * star r`.
-/
class StarMul (R : Type u) [Mul R] extends InvolutiveStar R where
  /-- `star` skew-distributes over multiplication. -/
  star_mul : ∀ r s : R, star (r * s) = star s * star r

export StarMul (star_mul)

attribute [simp 900] star_mul

section StarMul

variable [Mul R] [StarMul R]

theorem star_star_mul (x y : R) : star (star x * y) = star y * x := by rw [star_mul, star_star]

theorem star_mul_star (x y : R) : star (x * star y) = y * star x := by rw [star_mul, star_star]

@[simp]
theorem semiconjBy_star_star_star {x y z : R} :
    SemiconjBy (star x) (star z) (star y) ↔ SemiconjBy x y z := by
  simp_rw [SemiconjBy, ← star_mul, star_inj, eq_comm]

alias ⟨_, SemiconjBy.star_star_star⟩ := semiconjBy_star_star_star

@[simp]
theorem commute_star_star {x y : R} : Commute (star x) (star y) ↔ Commute x y :=
  semiconjBy_star_star_star

alias ⟨_, Commute.star_star⟩ := commute_star_star

theorem commute_star_comm {x y : R} : Commute (star x) y ↔ Commute x (star y) := by
  rw [← commute_star_star, star_star]

end StarMul

/-- In a commutative ring, make `simp` prefer leaving the order unchanged. -/
@[simp]
theorem star_mul' [CommMagma R] [StarMul R] (x y : R) : star (x * y) = star x * star y :=
  (star_mul x y).trans (mul_comm _ _)

/-- `star` as a `MulEquiv` from `R` to `Rᵐᵒᵖ` -/
@[simps apply]
def starMulEquiv [Mul R] [StarMul R] : R ≃* Rᵐᵒᵖ :=
  { (InvolutiveStar.star_involutive.toPerm star).trans opEquiv with
    toFun := fun x => MulOpposite.op (star x)
    map_mul' := fun x y => by simp only [star_mul, op_mul] }

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

/-- Any commutative monoid admits the trivial `*`-structure.

See note [reducible non-instances].
-/
abbrev starMulOfComm {R : Type*} [CommMonoid R] : StarMul R where
  star := id
  star_involutive _ := rfl
  star_mul := mul_comm

section

attribute [local instance] starMulOfComm

/-- Note that since `starMulOfComm` is reducible, `simp` can already prove this. -/
theorem star_id_of_comm {R : Type*} [CommMonoid R] {x : R} : star x = x :=
  rfl

end
