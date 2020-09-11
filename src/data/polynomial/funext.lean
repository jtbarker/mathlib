import data.polynomial.ring_division

namespace polynomial

variables {R : Type*} [integral_domain R]

lemma zero_of_eval_zero [hr : infinite R] (p : polynomial R) (h : ∀ x, p.eval x = 0) : p = 0 :=
by classical; by_contradiction hp; exact
  infinite.not_fintype ⟨p.roots.to_finset, λ x, multiset.mem_to_finset.mpr ((mem_roots hp).mpr (h _))⟩

lemma funext [infinite R] {p q : polynomial R} (ext : ∀ r : R, p.eval r = q.eval r) : p = q :=
begin
  rw ← sub_eq_zero,
  apply zero_of_eval_zero,
  intro x,
  rw [eval_sub, sub_eq_zero, ext],
end

end polynomial
