/-
Copyright (c) 2020 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import algebra.lie_algebra
import linear_algebra.tensor_algebra

/-!
# Univeral enveloping algebra

Given a commutative ring `R` and a Lie algebra `L` over `R`, we construct the universal
enveloping algebra of `L`, together its universal property.

## Main definitions

  * `universal_enveloping_algebra`
  * `universal_enveloping_algebra.algebra`
  * `universal_enveloping_algebra.lift`
  * `universal_enveloping_algebra.ι_comp_lift`
  * `universal_enveloping_algebra.lift_unique`

## Implementation notes

The universal enveloping algebra is constructed as a quotient of the tensor algebra using the
`quot` function. We take this low-level approach because at the time of writing, quotients of
non-commutative rings have not yet been defined. This approach means that we must manually construct
the algebraic structure on the quotient, but this turns out not to be much trouble.

We emphasise that the implementation is immaterial because the universal enveloping algebra is
characterised up to unique isomorphism by its universal property, which we also provide.

## Tags

lie algebra, universal enveloping algebra, tensor algebra
-/

universes u₁ u₂ u₃

variables (R : Type u₁) (L : Type u₂)
variables [comm_ring R] [lie_ring L] [lie_algebra R L]

namespace universal_enveloping_algebra

open tensor_algebra

/-- The quotient by the transitive closure of this relation is the universal enveloping algebra. -/
inductive rel : tensor_algebra R L → tensor_algebra R L → Prop
| lie_compat (x y : L) : rel (ι R L ⁅x, y⁆) ⁅ι R L x, ι R L y⁆
| add_compat {a b c} : rel a b → rel (a + c) (b + c)
| mul_compat_left {a b c} : rel a b → rel (a * c) (b * c)
| mul_compat_right {a b c} : rel a b → rel (c * a) (c * b)

end universal_enveloping_algebra

/-- The universal enveloping algebra of a Lie algebra. -/
def universal_enveloping_algebra := quot (universal_enveloping_algebra.rel R L)

namespace universal_enveloping_algebra

instance : ring (universal_enveloping_algebra R L) :=
{ add           := quot.map₂ (+)
    (λ c a b h, by { rw [add_comm c a, add_comm c b], exact rel.add_compat h, })
    (λ _ _ _, rel.add_compat),
  add_assoc     := by { rintros ⟨⟩ ⟨⟩ ⟨⟩, change quot.mk _ _ = _, rw add_assoc, refl, },
  zero          := quot.mk _ 0,
  zero_add      := by { rintros ⟨⟩, change quot.mk _ _ = _, rw zero_add, },
  add_zero      := by { rintros ⟨⟩, change quot.mk _ _ = _, rw add_zero, },
  add_comm      := by { rintros ⟨⟩ ⟨⟩, change quot.mk _ _ = _, rw add_comm, refl, },
  neg           := quot.map (λ a, -a)
    (λ a b h, by simp only [neg_eq_neg_one_mul a, neg_eq_neg_one_mul b, rel.mul_compat_right h]),
  add_left_neg  := by { rintros ⟨⟩, change quot.mk _ _ = _, rw add_left_neg, refl, },
  mul           := quot.map₂ (*) (λ _ _ _, rel.mul_compat_right) (λ _ _ _, rel.mul_compat_left),
  mul_assoc     := by { rintros ⟨⟩ ⟨⟩ ⟨⟩, change quot.mk _ _ = _, rw mul_assoc, refl, },
  one           := quot.mk _ 1,
  one_mul       := by { rintros ⟨⟩, change quot.mk _ _ = _, rw one_mul, },
  mul_one       := by { rintros ⟨⟩, change quot.mk _ _ = _, rw mul_one, },
  left_distrib  := by { rintros ⟨⟩ ⟨⟩ ⟨⟩, change quot.mk _ _ = _, rw left_distrib, refl, },
  right_distrib := by { rintros ⟨⟩ ⟨⟩ ⟨⟩, change quot.mk _ _ = _, rw right_distrib, refl, }, }

instance : algebra R (universal_enveloping_algebra R L) :=
{ smul      := λ r a, (quot.mk (rel R L) (r • 1)) * a,
  to_fun    := λ r, quot.mk _ (r • 1),
  map_one'  := by { rw one_smul, refl, },
  map_mul'  := λ r s, by { change _ = quot.mk _ _, simp [mul_smul], },
  map_zero' := by { rw zero_smul, refl, },
  map_add'  := λ r s, by { change _ = quot.mk _ _, rw add_smul, },
  commutes' := λ r, by { rintros ⟨a⟩, change quot.mk _ _ = quot.mk _ _, simp, },
  smul_def' := λ r u, rfl, }

instance : inhabited (universal_enveloping_algebra R L) := ⟨0⟩

/-- The quotient map from the tensor algebra to the universal enveloping algebra as a morphism of
associative algebras.

This map can be shown to exist using just universal properties but it is convenient to compromise
slightly and construct it directly as below. -/
def mk_alg_hom : tensor_algebra R L →ₐ[R] universal_enveloping_algebra R L :=
{ to_fun    := quot.mk (rel R L),
  map_one'  := rfl,
  map_mul'  := λ a b, rfl,
  map_zero' := rfl,
  map_add'  := λ a b, rfl,
  commutes' := λ r, show _ = quot.mk _ _, by rw [algebra.smul_def'', mul_one], }

/-- The natural Lie algebra morphism from a Lie to its universal enveloping algebra.

Note that the Lie algebra structure on the universal enveloping algebra arises from its associative
algebra structure via the ring commutator. -/
def ι : L →ₗ⁅R⁆ universal_enveloping_algebra R L :=
{ to_fun    := quot.mk (rel R L) ∘ (tensor_algebra.ι R L),
  map_add'  := λ x y, by simpa only [function.comp_app, linear_map.map_add],
  map_smul' := λ c x, show _ = quot.mk _ _, by simp,
  map_lie   := λ x y, quot.sound (rel.lie_compat x y), }

variables (A : Type u₃) [ring A] [algebra R A] (f : L →ₗ⁅R⁆ A)

/-- The universal property of the universal enveloping algebra: Lie algebra morphisms into
associative algebras lift to associative algebra morphisms from the universal enveloping algebra. -/
def lift : universal_enveloping_algebra R L →ₐ[R] A :=
{ to_fun    := λ a, quot.lift_on a (tensor_algebra.lift R L (f : L →ₗ[R] A))
    (λ a b h,
    begin
      induction h,
      { -- case universal_enveloping.rel.lie_compat
        rw [← alg_hom.to_linear_map_apply, ← linear_map.comp_apply, tensor_algebra.ι_comp_lift],
        change f _ = _, simpa [lie_ring.of_associative_ring_bracket], },
      { -- case universal_enveloping.rel.add_compat
        simp only [alg_hom.map_add, add_left_inj, h_ih], },
      { -- case universal_enveloping.rel.mul_compat_left
        simp only [alg_hom.map_mul, h_ih], },
      { -- case universal_enveloping.rel.mul_compat_right
        simp only [alg_hom.map_mul, h_ih], },
    end),
  map_one'  := show algebra_map _ _ _ = _, by rw ring_hom.map_one,
  map_mul'  := by { rintros ⟨⟩ ⟨⟩, change tensor_algebra.lift R L ↑f _ = _, rw alg_hom.map_mul, },
  map_zero' := show tensor_algebra.lift R L ↑f 0 = (0 : A), by rw alg_hom.map_zero,
  map_add'  := by { rintros ⟨⟩ ⟨⟩, change tensor_algebra.lift R L ↑f _ = _, rw alg_hom.map_add, },
  commutes' := λ r, show tensor_algebra.lift R L ↑f _ = _, by simp [algebra.smul_def''], }

lemma ι_comp_lift : (lift R L A f) ∘ (ι R L) = f :=
by { ext, refl, }

lemma lift_unique (g : universal_enveloping_algebra R L →ₐ[R] A) (h : g ∘ (ι R L) = f) :
  g = lift R L A f :=
begin
  let φ₁ := g.comp (mk_alg_hom R L),
  let φ₂ := (lift R L A f).comp (mk_alg_hom R L),
  suffices : φ₁ = φ₂,
    { ext u, rcases quot.exists_rep u with ⟨a, ha⟩, rw ← ha, change φ₁ a = φ₂ a, rw this, },
  have h₁ : φ₁ = tensor_algebra.lift R L f,
    { rw ← tensor_algebra.lift_unique, ext, change _ = f _, rw ← h, refl, },
  have h₂ : φ₂ = tensor_algebra.lift R L f,
    { rw ← tensor_algebra.lift_unique, ext, change _ = f _, rw ← ι_comp_lift R L A f, refl, },
  rw [h₁, h₂],
end

end universal_enveloping_algebra
