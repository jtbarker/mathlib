/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Patrick Stevens
-/
import data.nat.choose.basic
import tactic.linarith
import tactic.omega
import algebra.big_operators.ring
import algebra.big_operators.intervals
import algebra.big_operators.order
/-!
# Sums of binomial coefficients

This file includes variants of the binomial theorem and other results on sums of binomial
coefficients. Theorems whose proofs depend on such sums may also go in this file for import
reasons.

-/
open nat
open finset

open_locale big_operators

variables {α : Type*}

/-- A version of the binomial theorem for noncommutative semirings. -/
theorem commute.add_pow [semiring α] {x y : α} (h : commute x y) (n : ℕ) :
  (x + y) ^ n = ∑ m in range (n + 1), x ^ m * y ^ (n - m) * choose n m :=
begin
  let t : ℕ → ℕ → α := λ n m, x ^ m * (y ^ (n - m)) * (choose n m),
  change (x + y) ^ n = ∑ m in range (n + 1), t n m,
  have h_first : ∀ n, t n 0 = y ^ n :=
    λ n, by { dsimp [t], rw[choose_zero_right, nat.cast_one, mul_one, one_mul] },
  have h_last : ∀ n, t n n.succ = 0 :=
    λ n, by { dsimp [t], rw [choose_succ_self, nat.cast_zero, mul_zero] },
  have h_middle : ∀ (n i : ℕ), (i ∈ finset.range n.succ) →
   ((t n.succ) ∘ nat.succ) i = x * (t n i) + y * (t n i.succ) :=
  begin
    intros n i h_mem,
    have h_le : i ≤ n := nat.le_of_lt_succ (finset.mem_range.mp h_mem),
    dsimp [t],
    rw [choose_succ_succ, nat.cast_add, mul_add],
    congr' 1,
    { rw[pow_succ x, succ_sub_succ, mul_assoc, mul_assoc, mul_assoc] },
    { rw[← mul_assoc y, ← mul_assoc y, (h.symm.pow_right i.succ).eq],
      by_cases h_eq : i = n,
      { rw [h_eq, choose_succ_self, nat.cast_zero, mul_zero, mul_zero] },
      { rw[succ_sub (lt_of_le_of_ne h_le h_eq)],
        rw[pow_succ y, mul_assoc, mul_assoc, mul_assoc, mul_assoc] } }
  end,
  induction n with n ih,
  { rw [pow_zero, sum_range_succ, range_zero, sum_empty, add_zero],
    dsimp [t], rw [choose_self, nat.cast_one, mul_one, mul_one] },
  { rw[sum_range_succ', h_first],
    rw[finset.sum_congr rfl (h_middle n), finset.sum_add_distrib, add_assoc],
    rw[pow_succ (x + y), ih, add_mul, finset.mul_sum, finset.mul_sum],
    congr' 1,
    rw[finset.sum_range_succ', finset.sum_range_succ, h_first, h_last,
       mul_zero, zero_add, pow_succ] }
end

/-- The binomial theorem -/
theorem add_pow [comm_semiring α] (x y : α) (n : ℕ) :
  (x + y) ^ n = ∑ m in range (n + 1), x ^ m * y ^ (n - m) * choose n m :=
(commute.all x y).add_pow n

namespace nat

/-- The sum of entries in a row of Pascal's triangle -/
theorem sum_range_choose (n : ℕ) :
  ∑ m in range (n + 1), choose n m = 2 ^ n :=
by simpa using (add_pow 1 1 n).symm

lemma sum_range_choose_halfway (m : nat) :
  ∑ i in range (m + 1), choose (2 * m + 1) i = 4 ^ m :=
have ∑ i in range (m + 1), choose (2 * m + 1) (2 * m + 1 - i) =
  ∑ i in range (m + 1), choose (2 * m + 1) i,
from sum_congr rfl $ λ i hi, choose_symm $ by linarith [mem_range.1 hi],
(nat.mul_right_inj zero_lt_two).1 $
calc 2 * (∑ i in range (m + 1), choose (2 * m + 1) i) =
  (∑ i in range (m + 1), choose (2 * m + 1) i) +
    ∑ i in range (m + 1), choose (2 * m + 1) (2 * m + 1 - i) :
  by rw [two_mul, this]
... = (∑ i in range (m + 1), choose (2 * m + 1) i) +
  ∑ i in Ico (m + 1) (2 * m + 2), choose (2 * m + 1) i :
  by { rw [range_eq_Ico, sum_Ico_reflect], { congr, omega }, omega }
... = ∑ i in range (2 * m + 2), choose (2 * m + 1) i : sum_range_add_sum_Ico _ (by omega)
... = 2^(2 * m + 1) : sum_range_choose (2 * m + 1)
... = 2 * 4^m : by { rw [nat.pow_succ, mul_comm, nat.pow_mul], refl }

lemma choose_middle_le_pow (n : ℕ) : choose (2 * n + 1) n ≤ 4 ^ n :=
begin
  have t : choose (2 * n + 1) n ≤ ∑ i in range (n + 1), choose (2 * n + 1) i :=
    single_le_sum (λ x _, by linarith) (self_mem_range_succ n),
  simpa [sum_range_choose_halfway n] using t
end

end nat
