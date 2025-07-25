/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.Star

/-!
# Topological star (sub)algebras

A topological star algebra over a topological semiring `R` is a topological semiring with a
compatible continuous scalar multiplication by elements of `R` and a continuous star operation.
We reuse typeclass `ContinuousSMul` for topological algebras.

## Results

This is just a minimal stub for now!

The topological closure of a star subalgebra is still a star subalgebra,
which as a star algebra is a topological star algebra.
-/

open Topology
namespace StarSubalgebra

section TopologicalStarAlgebra

variable {R A B : Type*} [CommSemiring R] [StarRing R]
variable [TopologicalSpace A] [Semiring A] [Algebra R A] [StarRing A] [StarModule R A]

instance [IsTopologicalSemiring A] (s : StarSubalgebra R A) : IsTopologicalSemiring s :=
  s.toSubalgebra.topologicalSemiring

/-- The `StarSubalgebra.inclusion` of a star subalgebra is an embedding. -/
lemma isEmbedding_inclusion {S₁ S₂ : StarSubalgebra R A} (h : S₁ ≤ S₂) :
    IsEmbedding (inclusion h) where
  eq_induced := Eq.symm induced_compose
  injective := Subtype.map_injective h Function.injective_id

@[deprecated (since := "2024-10-26")]
alias embedding_inclusion := isEmbedding_inclusion

/-- The `StarSubalgebra.inclusion` of a closed star subalgebra is a `IsClosedEmbedding`. -/
theorem isClosedEmbedding_inclusion {S₁ S₂ : StarSubalgebra R A} (h : S₁ ≤ S₂)
    (hS₁ : IsClosed (S₁ : Set A)) : IsClosedEmbedding (inclusion h) :=
  { IsEmbedding.inclusion h with
    isClosed_range := isClosed_induced_iff.2
      ⟨S₁, hS₁, by
          convert (Set.range_subtype_map id _).symm
          · rw [Set.image_id]; rfl
          · intro _ h'
            apply h h' ⟩ }

variable [IsTopologicalSemiring A] [ContinuousStar A]
variable [TopologicalSpace B] [Semiring B] [Algebra R B] [StarRing B]

/-- The closure of a star subalgebra in a topological star algebra as a star subalgebra. -/
def topologicalClosure (s : StarSubalgebra R A) : StarSubalgebra R A :=
  {
    s.toSubalgebra.topologicalClosure with
    carrier := closure (s : Set A)
    star_mem' := fun ha =>
      map_mem_closure continuous_star ha fun x => (star_mem : x ∈ s → star x ∈ s) }

theorem topologicalClosure_toSubalgebra_comm (s : StarSubalgebra R A) :
    s.topologicalClosure.toSubalgebra = s.toSubalgebra.topologicalClosure :=
  SetLike.coe_injective rfl

@[simp]
theorem topologicalClosure_coe (s : StarSubalgebra R A) :
    (s.topologicalClosure : Set A) = closure (s : Set A) :=
  rfl

theorem le_topologicalClosure (s : StarSubalgebra R A) : s ≤ s.topologicalClosure :=
  subset_closure

theorem isClosed_topologicalClosure (s : StarSubalgebra R A) :
    IsClosed (s.topologicalClosure : Set A) :=
  isClosed_closure

instance {A : Type*} [UniformSpace A] [CompleteSpace A] [Semiring A] [StarRing A]
    [IsTopologicalSemiring A] [ContinuousStar A] [Algebra R A] [StarModule R A]
    {S : StarSubalgebra R A} : CompleteSpace S.topologicalClosure :=
  isClosed_closure.completeSpace_coe

theorem topologicalClosure_minimal {s t : StarSubalgebra R A} (h : s ≤ t)
    (ht : IsClosed (t : Set A)) : s.topologicalClosure ≤ t :=
  closure_minimal h ht

theorem topologicalClosure_mono : Monotone (topologicalClosure : _ → StarSubalgebra R A) :=
  fun _ S₂ h =>
  topologicalClosure_minimal (h.trans <| le_topologicalClosure S₂) (isClosed_topologicalClosure S₂)

theorem topologicalClosure_map_le [StarModule R B] [IsTopologicalSemiring B] [ContinuousStar B]
    (s : StarSubalgebra R A) (φ : A →⋆ₐ[R] B) (hφ : IsClosedMap φ) :
    (map φ s).topologicalClosure ≤ map φ s.topologicalClosure :=
  hφ.closure_image_subset _

theorem map_topologicalClosure_le [StarModule R B] [IsTopologicalSemiring B] [ContinuousStar B]
    (s : StarSubalgebra R A) (φ : A →⋆ₐ[R] B) (hφ : Continuous φ) :
    map φ s.topologicalClosure ≤ (map φ s).topologicalClosure :=
  image_closure_subset_closure_image hφ

theorem topologicalClosure_map [StarModule R B] [IsTopologicalSemiring B] [ContinuousStar B]
    (s : StarSubalgebra R A) (φ : A →⋆ₐ[R] B) (hφ : IsClosedEmbedding φ) :
    (map φ s).topologicalClosure = map φ s.topologicalClosure :=
  SetLike.coe_injective <| hφ.closure_image_eq _

theorem _root_.Subalgebra.topologicalClosure_star_comm (s : Subalgebra R A) :
    (star s).topologicalClosure = star s.topologicalClosure := by
  suffices ∀ t : Subalgebra R A, (star t).topologicalClosure ≤ star t.topologicalClosure from
    le_antisymm (this s) (by simpa only [star_star] using Subalgebra.star_mono (this (star s)))
  exact fun t => (star t).topologicalClosure_minimal (Subalgebra.star_mono subset_closure)
    (isClosed_closure.preimage continuous_star)

/-- If a star subalgebra of a topological star algebra is commutative, then so is its topological
closure. See note [reducible non-instances]. -/
abbrev commSemiringTopologicalClosure [T2Space A] (s : StarSubalgebra R A)
    (hs : ∀ x y : s, x * y = y * x) : CommSemiring s.topologicalClosure :=
  s.toSubalgebra.commSemiringTopologicalClosure hs

/-- If a star subalgebra of a topological star algebra is commutative, then so is its topological
closure. See note [reducible non-instances]. -/
abbrev commRingTopologicalClosure {R A} [CommRing R] [StarRing R] [TopologicalSpace A] [Ring A]
    [Algebra R A] [StarRing A] [StarModule R A] [IsTopologicalRing A] [ContinuousStar A] [T2Space A]
    (s : StarSubalgebra R A) (hs : ∀ x y : s, x * y = y * x) : CommRing s.topologicalClosure :=
  s.toSubalgebra.commRingTopologicalClosure hs

/-- Continuous `StarAlgHom`s from the topological closure of a `StarSubalgebra` whose
compositions with the `StarSubalgebra.inclusion` map agree are, in fact, equal. -/
theorem _root_.StarAlgHom.ext_topologicalClosure [T2Space B] {S : StarSubalgebra R A}
    {φ ψ : S.topologicalClosure →⋆ₐ[R] B} (hφ : Continuous φ) (hψ : Continuous ψ)
    (h :
      φ.comp (inclusion (le_topologicalClosure S)) = ψ.comp (inclusion (le_topologicalClosure S))) :
    φ = ψ := by
  rw [DFunLike.ext'_iff]
  have : Dense (Set.range <| inclusion (le_topologicalClosure S)) := by
    refine IsInducing.subtypeVal.dense_iff.2 fun x => ?_
    convert show ↑x ∈ closure (S : Set A) from x.prop
    rw [← Set.range_comp]
    exact
      Set.ext fun y =>
        ⟨by
          rintro ⟨y, rfl⟩
          exact y.prop, fun hy => ⟨⟨y, hy⟩, rfl⟩⟩
  refine Continuous.ext_on this hφ hψ ?_
  rintro _ ⟨x, rfl⟩
  simpa only using DFunLike.congr_fun h x

theorem _root_.StarAlgHomClass.ext_topologicalClosure [T2Space B] {F : Type*}
    {S : StarSubalgebra R A} [FunLike F S.topologicalClosure B]
    [AlgHomClass F R S.topologicalClosure B] [StarHomClass F S.topologicalClosure B] {φ ψ : F}
    (hφ : Continuous φ) (hψ : Continuous ψ) (h : ∀ x : S,
        φ (inclusion (le_topologicalClosure S) x) = ψ ((inclusion (le_topologicalClosure S)) x)) :
    φ = ψ := by
  have : (φ : S.topologicalClosure →⋆ₐ[R] B) = (ψ : S.topologicalClosure →⋆ₐ[R] B) := by
    refine StarAlgHom.ext_topologicalClosure (R := R) (A := A) (B := B) hφ hψ (StarAlgHom.ext ?_)
    simpa only [StarAlgHom.coe_comp, StarAlgHom.coe_coe] using h
  rw [DFunLike.ext'_iff, ← StarAlgHom.coe_coe]
  apply congrArg _ this

end TopologicalStarAlgebra

end StarSubalgebra

section Elemental

namespace StarAlgebra

open StarSubalgebra

variable (R : Type*) {A B : Type*} [CommSemiring R] [StarRing R]
variable [TopologicalSpace A] [Semiring A] [StarRing A] [IsTopologicalSemiring A]
variable [ContinuousStar A] [Algebra R A] [StarModule R A]
variable [TopologicalSpace B] [Semiring B] [StarRing B] [Algebra R B]

/-- The topological closure of the star subalgebra generated by a single element. -/
def elemental (x : A) : StarSubalgebra R A :=
  (adjoin R ({x} : Set A)).topologicalClosure

@[deprecated (since := "2024-11-05")] alias _root_.elementalStarAlgebra := elemental

namespace elemental

@[simp, aesop safe (rule_sets := [SetLike])]
theorem self_mem (x : A) : x ∈ elemental R x :=
  le_topologicalClosure _ (self_mem_adjoin_singleton R x)

@[deprecated (since := "2024-11-05")] alias _root_.elementalStarAlgebra.self_mem := self_mem

@[simp, aesop safe (rule_sets := [SetLike])]
theorem star_self_mem (x : A) : star x ∈ elemental R x :=
  star_mem <| self_mem R x

@[deprecated (since := "2024-11-05")]
alias _root_.elementalStarAlgebra.star_self_mem := star_self_mem

/-- The `elemental` star subalgebra generated by a normal element is commutative. -/
instance [T2Space A] {x : A} [IsStarNormal x] : CommSemiring (elemental R x) :=
  StarSubalgebra.commSemiringTopologicalClosure _ mul_comm

/-- The `elemental` generated by a normal element is commutative. -/
instance {R A} [CommRing R] [StarRing R] [TopologicalSpace A] [Ring A] [Algebra R A] [StarRing A]
    [StarModule R A] [IsTopologicalRing A] [ContinuousStar A] [T2Space A] {x : A} [IsStarNormal x] :
    CommRing (elemental R x) :=
  StarSubalgebra.commRingTopologicalClosure _ mul_comm

theorem isClosed (x : A) : IsClosed (elemental R x : Set A) :=
  isClosed_closure

@[deprecated (since := "2024-11-05")] alias _root_.elementalStarAlgebra.isClosed := isClosed

instance {A : Type*} [UniformSpace A] [CompleteSpace A] [Semiring A] [StarRing A]
    [IsTopologicalSemiring A] [ContinuousStar A] [Algebra R A] [StarModule R A] (x : A) :
    CompleteSpace (elemental R x) :=
  isClosed_closure.completeSpace_coe

variable {R} in
theorem le_of_mem {S : StarSubalgebra R A} (hS : IsClosed (S : Set A)) {x : A}
    (hx : x ∈ S) : elemental R x ≤ S :=
  topologicalClosure_minimal (adjoin_le <| Set.singleton_subset_iff.2 hx) hS

variable {R} in
theorem le_iff_mem {x : A} {s : StarSubalgebra R A} (hs : IsClosed (s : Set A)) :
    elemental R x ≤ s ↔ x ∈ s :=
  ⟨fun h ↦ h (self_mem R x), fun h ↦ le_of_mem hs h⟩

@[deprecated (since := "2024-11-05")]
alias _root_.elementalStarAlgebra.le_of_isClosed_of_mem := le_of_mem

/-- The coercion from an elemental algebra to the full algebra as a `IsClosedEmbedding`. -/
theorem isClosedEmbedding_coe (x : A) : IsClosedEmbedding ((↑) : elemental R x → A) where
  eq_induced := rfl
  injective := Subtype.coe_injective
  isClosed_range := by simpa using isClosed R x

@[deprecated (since := "2024-11-05")]
alias _root_.elementalStarAlgebra.isClosedEmbedding_coe := isClosedEmbedding_coe
@[elab_as_elim]
theorem induction_on {x y : A}
    (hy : y ∈ elemental R x) {P : (u : A) → u ∈ elemental R x → Prop}
    (self : P x (self_mem R x)) (star_self : P (star x) (star_self_mem R x))
    (algebraMap : ∀ r, P (algebraMap R A r) (_root_.algebraMap_mem _ r))
    (add : ∀ u hu v hv, P u hu → P v hv → P (u + v) (add_mem hu hv))
    (mul : ∀ u hu v hv, P u hu → P v hv → P (u * v) (mul_mem hu hv))
    (closure : ∀ s : Set A, (hs : s ⊆ elemental R x) → (∀ u, (hu : u ∈ s) →
      P u (hs hu)) → ∀ v, (hv : v ∈ closure s) → P v (closure_minimal hs (isClosed R x) hv)) :
    P y hy := by
  apply closure (adjoin R {x} : Set A) subset_closure (fun y hy ↦ ?_) y hy
  rw [SetLike.mem_coe, ← mem_toSubalgebra, adjoin_toSubalgebra] at hy
  induction hy using Algebra.adjoin_induction with
  | mem u hu =>
    obtain ((rfl : u = x) | (hu : star u = x)) := by simpa using hu
    · exact self
    · simp_rw [← hu, star_star] at star_self
      exact star_self
  | algebraMap r => exact algebraMap r
  | add u v hu_mem hv_mem hu hv =>
    exact add u (subset_closure hu_mem) v (subset_closure hv_mem) (hu hu_mem) (hv hv_mem)
  | mul u v hu_mem hv_mem hu hv =>
    exact mul u (subset_closure hu_mem) v (subset_closure hv_mem) (hu hu_mem) (hv hv_mem)

@[deprecated (since := "2024-11-05")]
alias _root_.elementalStarAlgebra.induction_on := induction_on

theorem starAlgHomClass_ext [T2Space B] {F : Type*} {a : A}
    [FunLike F (elemental R a) B] [AlgHomClass F R _ B] [StarHomClass F _ B]
    {φ ψ : F} (hφ : Continuous φ)
    (hψ : Continuous ψ) (h : φ ⟨a, self_mem R a⟩ = ψ ⟨a, self_mem R a⟩) : φ = ψ := by
  refine StarAlgHomClass.ext_topologicalClosure hφ hψ fun x => ?_
  refine adjoin_induction_subtype x ?_ ?_ ?_ ?_ ?_
  exacts [fun y hy => by simpa only [Set.mem_singleton_iff.mp hy] using h, fun r => by
    simp only [AlgHomClass.commutes], fun x y hx hy => by simp only [map_add, hx, hy],
    fun x y hx hy => by simp only [map_mul, hx, hy], fun x hx => by simp only [map_star, hx]]

@[deprecated (since := "2024-11-05")]
alias _root_.elementalStarAlgebra.starAlgHomClass_ext := starAlgHomClass_ext

end elemental

end StarAlgebra

end Elemental
