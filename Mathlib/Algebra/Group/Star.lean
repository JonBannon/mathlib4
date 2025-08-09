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
import Mathlib.Algebra.Star.Defs

/-!
# Star monoids

Write this.

-/

universe u v w

variable {R : Type u}

open MulOpposite

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
