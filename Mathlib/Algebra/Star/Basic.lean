/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Mathlib.Algebra.Star.Defs

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

universe u v w

open MulOpposite

variable {R : Type u}

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

theorem eq_star_of_eq_star [InvolutiveStar R] {r s : R} (h : r = star s) : s = star r := by
  simp [h]

theorem eq_star_iff_eq_star [InvolutiveStar R] {r s : R} : r = star s ↔ s = star r :=
  ⟨eq_star_of_eq_star, eq_star_of_eq_star⟩

theorem star_eq_iff_star_eq [InvolutiveStar R] {r s : R} : star r = s ↔ star s = r :=
  eq_comm.trans <| eq_star_iff_eq_star.trans eq_comm

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
